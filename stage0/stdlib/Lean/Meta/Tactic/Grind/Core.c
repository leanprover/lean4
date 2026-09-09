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
lean_object* v___x_217_; double v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_219_ = 0;
v___x_220_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_221_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_221_, 0, v_cls_186_);
lean_ctor_set(v___x_221_, 1, v___x_217_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3, v___x_218_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3 + 8, v___x_218_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*3 + 16, v___x_219_);
v___x_222_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_223_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v_a_195_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_inc(v_ref_193_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_193_);
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
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_env_201_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_nextMacroScope_202_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_ngen_203_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_auxDeclNGen_204_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_cache_205_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_messages_206_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v_infoState_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_snapshotTasks_208_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_st_ref_put(v___y_191_, v___x_229_);
v___x_231_ = lean_box(0);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_231_);
v___x_233_ = v___x_197_;
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
size_t v_x_22515__boxed_352_; lean_object* v_res_353_; 
v_x_22515__boxed_352_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_348_, v_x_349_, v_x_22515__boxed_352_, v_x_351_);
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
size_t v_x_22977__boxed_605_; lean_object* v_res_606_; 
v_x_22977__boxed_605_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_res_606_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_600_, v_00_u03b2_601_, v_x_602_, v_x_22977__boxed_605_, v_x_604_);
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
size_t v_x_9678__boxed_786_; uint8_t v_res_787_; lean_object* v_r_788_; 
v_x_9678__boxed_786_ = lean_unbox_usize(v_x_784_);
lean_dec(v_x_784_);
v_res_787_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_783_, v_x_9678__boxed_786_, v_x_785_);
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
size_t v_x_9961__boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_x_9961__boxed_954_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_950_, v_x_951_, v_x_9961__boxed_954_, v_x_953_);
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
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_984_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1000_ = l_Lean_Expr_appArg_x21(v_a_996_);
lean_dec(v_a_996_);
v___x_1001_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_992_);
v___x_1002_ = l_Lean_mkApp3(v___x_999_, v_a_992_, v___x_1000_, v___x_1001_);
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1004_ = l_Lean_mkApp4(v___x_1003_, v_a_992_, v_a_998_, v___x_1002_, v_a_994_);
v___x_1005_ = l_Lean_Meta_Grind_closeGoal(v___x_1004_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_996_);
lean_dec(v_a_994_);
lean_dec(v_a_992_);
v_a_1006_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_997_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_997_);
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
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_head_1067_ = lean_ctor_get(v_as_x27_1053_, 0);
v_tail_1068_ = lean_ctor_get(v_as_x27_1053_, 1);
v___x_1069_ = lean_st_ref_get(v___y_1055_);
lean_inc(v_head_1067_);
v___x_1070_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1069_, v_head_1067_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___x_1069_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_self_1072_; lean_object* v_next_1073_; lean_object* v_root_1074_; lean_object* v_congr_1075_; lean_object* v_target_x3f_1076_; lean_object* v_proof_x3f_1077_; uint8_t v_flipped_1078_; lean_object* v_size_1079_; uint8_t v_interpreted_1080_; uint8_t v_ctor_1081_; uint8_t v_hasLambdas_1082_; uint8_t v_heqProofs_1083_; lean_object* v_idx_1084_; lean_object* v_generation_1085_; lean_object* v_mt_1086_; lean_object* v_sTerms_1087_; uint8_t v_funCC_1088_; lean_object* v_ematchDiagSource_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1102_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_self_1072_ = lean_ctor_get(v_a_1071_, 0);
v_next_1073_ = lean_ctor_get(v_a_1071_, 1);
v_root_1074_ = lean_ctor_get(v_a_1071_, 2);
v_congr_1075_ = lean_ctor_get(v_a_1071_, 3);
v_target_x3f_1076_ = lean_ctor_get(v_a_1071_, 4);
v_proof_x3f_1077_ = lean_ctor_get(v_a_1071_, 5);
v_flipped_1078_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12);
v_size_1079_ = lean_ctor_get(v_a_1071_, 6);
v_interpreted_1080_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12 + 1);
v_ctor_1081_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12 + 2);
v_hasLambdas_1082_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12 + 3);
v_heqProofs_1083_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12 + 4);
v_idx_1084_ = lean_ctor_get(v_a_1071_, 7);
v_generation_1085_ = lean_ctor_get(v_a_1071_, 8);
v_mt_1086_ = lean_ctor_get(v_a_1071_, 9);
v_sTerms_1087_ = lean_ctor_get(v_a_1071_, 10);
v_funCC_1088_ = lean_ctor_get_uint8(v_a_1071_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1089_ = lean_ctor_get(v_a_1071_, 11);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1071_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1091_ = v_a_1071_;
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_ematchDiagSource_1089_);
lean_inc(v_sTerms_1087_);
lean_inc(v_mt_1086_);
lean_inc(v_generation_1085_);
lean_inc(v_idx_1084_);
lean_inc(v_size_1079_);
lean_inc(v_proof_x3f_1077_);
lean_inc(v_target_x3f_1076_);
lean_inc(v_congr_1075_);
lean_inc(v_root_1074_);
lean_inc(v_next_1073_);
lean_inc(v_self_1072_);
lean_dec(v_a_1071_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_lt(v_mt_1086_, v___x_1052_);
lean_dec(v_mt_1086_);
if (v___x_1094_ == 0)
{
lean_del_object(v___x_1091_);
lean_dec(v_ematchDiagSource_1089_);
lean_dec(v_sTerms_1087_);
lean_dec(v_generation_1085_);
lean_dec(v_idx_1084_);
lean_dec(v_size_1079_);
lean_dec(v_proof_x3f_1077_);
lean_dec(v_target_x3f_1076_);
lean_dec_ref(v_congr_1075_);
lean_dec_ref(v_root_1074_);
lean_dec_ref(v_next_1073_);
lean_dec_ref(v_self_1072_);
v_as_x27_1053_ = v_tail_1068_;
v_b_1054_ = v___x_1093_;
goto _start;
}
else
{
lean_object* v___x_1097_; 
lean_inc(v___x_1052_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 9, v___x_1052_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_self_1072_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_next_1073_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_root_1074_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_congr_1075_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_target_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1101_, 5, v_proof_x3f_1077_);
lean_ctor_set(v_reuseFailAlloc_1101_, 6, v_size_1079_);
lean_ctor_set(v_reuseFailAlloc_1101_, 7, v_idx_1084_);
lean_ctor_set(v_reuseFailAlloc_1101_, 8, v_generation_1085_);
lean_ctor_set(v_reuseFailAlloc_1101_, 9, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1101_, 10, v_sTerms_1087_);
lean_ctor_set(v_reuseFailAlloc_1101_, 11, v_ematchDiagSource_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12, v_flipped_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 1, v_interpreted_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 2, v_ctor_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 3, v_hasLambdas_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 4, v_heqProofs_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 5, v_funCC_1088_);
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
v_b_1054_ = v___x_1093_;
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
v_a_1103_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1070_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1070_);
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
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_st_ref_get(v_a_1112_);
v___x_1124_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_toGoalState_1125_; lean_object* v_ematch_1126_; lean_object* v_a_1127_; lean_object* v_gmt_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_toGoalState_1125_ = lean_ctor_get(v___x_1123_, 0);
lean_inc_ref(v_toGoalState_1125_);
lean_dec(v___x_1123_);
v_ematch_1126_ = lean_ctor_get(v_toGoalState_1125_, 12);
lean_inc_ref(v_ematch_1126_);
lean_dec_ref(v_toGoalState_1125_);
v_a_1127_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1124_, 1);
v_gmt_1128_ = lean_ctor_get(v_ematch_1126_, 1);
lean_inc(v_gmt_1128_);
lean_dec_ref(v_ematch_1126_);
v___x_1129_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1127_);
lean_dec(v_a_1127_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1128_, v___x_1129_, v___x_1130_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
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
lean_dec(v___x_1123_);
v_a_1140_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1124_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1124_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_fst_1227_, lean_object* v_lams_1228_, lean_object* v_____r_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1224_, v_a_1225_, v___y_1230_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; uint8_t v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___x_1290_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
if (v___x_1290_ == 0)
{
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_inc(v_fst_1227_);
v___x_1291_ = l_Array_reverse___redArg(v_fst_1227_);
lean_inc(v_snd_1224_);
v___x_1292_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1228_, v_snd_1224_, v___x_1291_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_dec_ref_known(v___x_1292_, 1);
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
goto v___jp_1241_;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_fst_1227_);
lean_dec(v_snd_1224_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_fst_1227_);
lean_dec(v_snd_1224_);
v_a_1301_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1288_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1288_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
v___jp_1241_:
{
if (lean_obj_tag(v_snd_1224_) == 5)
{
lean_object* v_fn_1252_; lean_object* v_arg_1253_; lean_object* v___x_1254_; 
v_fn_1252_ = lean_ctor_get(v_snd_1224_, 0);
lean_inc_ref(v_fn_1252_);
v_arg_1253_ = lean_ctor_get(v_snd_1224_, 1);
lean_inc_ref(v_arg_1253_);
v___x_1254_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1226_, v___y_1242_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_box(0);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc(v___y_1242_);
v___x_1257_ = lean_grind_internalize(v_snd_1224_, v_a_1255_, v___x_1256_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1267_; 
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1268_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1267_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1267_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1261_ = lean_array_push(v_fst_1227_, v_arg_1253_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_fn_1252_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1263_);
v___x_1265_ = v___x_1259_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_fn_1252_);
lean_dec(v_fst_1227_);
v_a_1269_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1257_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1257_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_fn_1252_);
lean_dec_ref_known(v_snd_1224_, 2);
lean_dec(v_fst_1227_);
v_a_1277_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1254_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1254_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_fst_1227_);
lean_ctor_set(v___x_1285_, 1, v_snd_1224_);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1309_ = _args[0];
lean_object* v_a_1310_ = _args[1];
lean_object* v_a_1311_ = _args[2];
lean_object* v_fst_1312_ = _args[3];
lean_object* v_lams_1313_ = _args[4];
lean_object* v_____r_1314_ = _args[5];
lean_object* v___y_1315_ = _args[6];
lean_object* v___y_1316_ = _args[7];
lean_object* v___y_1317_ = _args[8];
lean_object* v___y_1318_ = _args[9];
lean_object* v___y_1319_ = _args[10];
lean_object* v___y_1320_ = _args[11];
lean_object* v___y_1321_ = _args[12];
lean_object* v___y_1322_ = _args[13];
lean_object* v___y_1323_ = _args[14];
lean_object* v___y_1324_ = _args[15];
lean_object* v___y_1325_ = _args[16];
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1309_, v_a_1310_, v_a_1311_, v_fst_1312_, v_lams_1313_, v_____r_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v_lams_1313_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1326_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1333_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1334_ = l_Lean_Name_append(v___x_1333_, v___x_1332_);
return v___x_1334_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_lams_1340_, lean_object* v_a_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___y_1354_; lean_object* v_toCold_1374_; lean_object* v_options_1375_; lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1414_; 
v_toCold_1374_ = lean_ctor_get(v___y_1350_, 0);
v_options_1375_ = lean_ctor_get(v_toCold_1374_, 2);
v_fst_1376_ = lean_ctor_get(v_a_1341_, 0);
v_snd_1377_ = lean_ctor_get(v_a_1341_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1379_ = v_a_1341_;
v_isShared_1380_ = v_isSharedCheck_1414_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_snd_1377_);
lean_inc(v_fst_1376_);
lean_dec(v_a_1341_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1414_;
goto v_resetjp_1378_;
}
v___jp_1353_:
{
if (lean_obj_tag(v___y_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1365_; 
v_a_1355_ = lean_ctor_get(v___y_1354_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___y_1354_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1357_ = v___y_1354_;
v_isShared_1358_ = v_isSharedCheck_1365_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___y_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1365_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_a_1355_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v_a_1355_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v_a_1355_, 1);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_a_1359_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v_a_1363_; 
lean_del_object(v___x_1357_);
v_a_1363_ = lean_ctor_get(v_a_1355_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v_a_1355_, 1);
v_a_1341_ = v_a_1363_;
goto _start;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___y_1354_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___y_1354_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___y_1354_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___y_1354_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
v_resetjp_1378_:
{
lean_object* v_inheritedTraceOptions_1381_; uint8_t v_hasTrace_1382_; 
v_inheritedTraceOptions_1381_ = lean_ctor_get(v_toCold_1374_, 11);
v_hasTrace_1382_ = lean_ctor_get_uint8(v_options_1375_, sizeof(void*)*1);
if (v_hasTrace_1382_ == 0)
{
lean_del_object(v___x_1379_);
goto v___jp_1383_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1387_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1388_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1381_, v_options_1375_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_del_object(v___x_1379_);
goto v___jp_1383_;
}
else
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Meta_Grind_updateLastTag(v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec_ref_known(v___x_1389_, 1);
v___x_1390_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1377_);
v___x_1391_ = l_Lean_MessageData_ofExpr(v_snd_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set_tag(v___x_1379_, 7);
lean_ctor_set(v___x_1379_, 1, v___x_1391_);
lean_ctor_set(v___x_1379_, 0, v___x_1390_);
v___x_1393_ = v___x_1379_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1386_, v___x_1393_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1377_, v_a_1339_, v_a_1338_, v_fst_1376_, v_lams_1340_, v_a_1395_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1354_ = v___x_1396_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_snd_1377_);
lean_dec(v_fst_1376_);
v_a_1397_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1394_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1394_);
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
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1379_);
lean_dec(v_snd_1377_);
lean_dec(v_fst_1376_);
v_a_1406_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1389_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1389_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_box(0);
v___x_1385_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1377_, v_a_1339_, v_a_1338_, v_fst_1376_, v_lams_1340_, v___x_1384_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1354_ = v___x_1385_;
goto v___jp_1353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_lams_1417_, lean_object* v_a_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1415_, v_a_1416_, v_lams_1417_, v_a_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v_lams_1417_);
lean_dec_ref(v_a_1416_);
lean_dec_ref(v_a_1415_);
return v_res_1430_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1436_, lean_object* v_lams_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
if (lean_obj_tag(v_as_x27_1438_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_b_1439_);
return v___x_1451_;
}
else
{
lean_object* v_toCold_1452_; lean_object* v_options_1453_; lean_object* v_head_1454_; lean_object* v_tail_1455_; lean_object* v_inheritedTraceOptions_1456_; uint8_t v_hasTrace_1457_; lean_object* v___x_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1482_; uint8_t v_a_1484_; 
v_toCold_1452_ = lean_ctor_get(v___y_1448_, 0);
v_options_1453_ = lean_ctor_get(v_toCold_1452_, 2);
v_head_1454_ = lean_ctor_get(v_as_x27_1438_, 0);
v_tail_1455_ = lean_ctor_get(v_as_x27_1438_, 1);
v_inheritedTraceOptions_1456_ = lean_ctor_get(v_toCold_1452_, 11);
v_hasTrace_1457_ = lean_ctor_get_uint8(v_options_1453_, sizeof(void*)*1);
v___x_1458_ = lean_box(0);
v___x_1482_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
if (v_hasTrace_1457_ == 0)
{
v_a_1484_ = v_hasTrace_1457_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1456_, v_options_1453_, v___x_1491_);
v_a_1484_ = v___x_1492_;
goto v___jp_1483_;
}
v___jp_1459_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v_head_1454_);
lean_inc_ref(v___y_1460_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___y_1460_);
lean_ctor_set(v___x_1471_, 1, v_head_1454_);
v___x_1472_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1454_, v_a_1436_, v_lams_1437_, v___x_1471_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_dec_ref_known(v___x_1472_, 1);
v_as_x27_1438_ = v_tail_1455_;
v_b_1439_ = v___x_1458_;
goto _start;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1472_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1472_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
v___jp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1484_ == 0)
{
v___y_1460_ = v___x_1485_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
v___y_1469_ = v___y_1448_;
v___y_1470_ = v___y_1449_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Meta_Grind_updateLastTag(v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref_known(v___x_1486_, 1);
v___x_1487_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1454_);
v___x_1488_ = l_Lean_MessageData_ofExpr(v_head_1454_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1482_, v___x_1489_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_dec_ref_known(v___x_1490_, 1);
v___y_1460_ = v___x_1485_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
v___y_1469_ = v___y_1448_;
v___y_1470_ = v___y_1449_;
goto v___jp_1459_;
}
else
{
return v___x_1490_;
}
}
else
{
return v___x_1486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1493_, lean_object* v_lams_1494_, lean_object* v_as_x27_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1493_, v_lams_1494_, v_as_x27_1495_, v_b_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v_as_x27_1495_);
lean_dec_ref(v_lams_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1509_, lean_object* v_lams_1510_, lean_object* v_as_1511_, lean_object* v_as_x27_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
if (lean_obj_tag(v_as_x27_1512_) == 0)
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1513_);
return v___x_1525_;
}
else
{
lean_object* v_toCold_1526_; lean_object* v_options_1527_; lean_object* v_head_1528_; lean_object* v_tail_1529_; lean_object* v_inheritedTraceOptions_1530_; uint8_t v_hasTrace_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v_a_1558_; 
v_toCold_1526_ = lean_ctor_get(v___y_1522_, 0);
v_options_1527_ = lean_ctor_get(v_toCold_1526_, 2);
v_head_1528_ = lean_ctor_get(v_as_x27_1512_, 0);
v_tail_1529_ = lean_ctor_get(v_as_x27_1512_, 1);
v_inheritedTraceOptions_1530_ = lean_ctor_get(v_toCold_1526_, 11);
v_hasTrace_1531_ = lean_ctor_get_uint8(v_options_1527_, sizeof(void*)*1);
v___x_1532_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1533_ = lean_box(0);
if (v_hasTrace_1531_ == 0)
{
v_a_1558_ = v_hasTrace_1531_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
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
v___x_1547_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1528_, v_a_1509_, v_lams_1510_, v___x_1546_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v___x_1547_, 1);
v___x_1548_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1509_, v_lams_1510_, v_tail_1529_, v___x_1533_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
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
v___y_1536_ = v___y_1514_;
v___y_1537_ = v___y_1515_;
v___y_1538_ = v___y_1516_;
v___y_1539_ = v___y_1517_;
v___y_1540_ = v___y_1518_;
v___y_1541_ = v___y_1519_;
v___y_1542_ = v___y_1520_;
v___y_1543_ = v___y_1521_;
v___y_1544_ = v___y_1522_;
v___y_1545_ = v___y_1523_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Grind_updateLastTag(v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
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
v___x_1564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1532_, v___x_1563_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref_known(v___x_1564_, 1);
v___y_1535_ = v___x_1559_;
v___y_1536_ = v___y_1514_;
v___y_1537_ = v___y_1515_;
v___y_1538_ = v___y_1516_;
v___y_1539_ = v___y_1517_;
v___y_1540_ = v___y_1518_;
v___y_1541_ = v___y_1519_;
v___y_1542_ = v___y_1520_;
v___y_1543_ = v___y_1521_;
v___y_1544_ = v___y_1522_;
v___y_1545_ = v___y_1523_;
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
lean_object* v_toCold_1609_; lean_object* v_options_1610_; lean_object* v_inheritedTraceOptions_1611_; uint8_t v_hasTrace_1612_; lean_object* v___x_1613_; lean_object* v_a_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; 
v_toCold_1609_ = lean_ctor_get(v___y_1604_, 0);
v_options_1610_ = lean_ctor_get(v_toCold_1609_, 2);
v_inheritedTraceOptions_1611_ = lean_ctor_get(v_toCold_1609_, 11);
v_hasTrace_1612_ = lean_ctor_get_uint8(v_options_1610_, sizeof(void*)*1);
v___x_1613_ = lean_box(0);
v_a_1614_ = lean_array_uget_borrowed(v_as_1592_, v_i_1594_);
if (v_hasTrace_1612_ == 0)
{
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1642_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1611_, v_options_1610_, v___x_1642_);
if (v___x_1643_ == 0)
{
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Grind_updateLastTag(v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; 
lean_dec_ref_known(v___x_1644_, 1);
v___x_1645_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1614_, v___y_1596_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
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
v___x_1657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1641_, v___x_1656_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_dec_ref_known(v___x_1657_, 1);
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
v___y_1625_ = v___y_1605_;
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
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1627_);
lean_dec(v_a_1627_);
v___x_1629_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1590_, v_lams_1591_, v___x_1628_, v___x_1628_, v___x_1613_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
size_t v___x_1630_; size_t v___x_1631_; 
lean_dec_ref_known(v___x_1629_, 1);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1594_, v___x_1630_);
v_i_1594_ = v___x_1631_;
v_b_1595_ = v___x_1613_;
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
lean_object* v_toCold_1705_; lean_object* v_options_1706_; lean_object* v_inheritedTraceOptions_1707_; uint8_t v_hasTrace_1708_; lean_object* v___x_1709_; lean_object* v_a_1710_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; 
v_toCold_1705_ = lean_ctor_get(v___y_1700_, 0);
v_options_1706_ = lean_ctor_get(v_toCold_1705_, 2);
v_inheritedTraceOptions_1707_ = lean_ctor_get(v_toCold_1705_, 11);
v_hasTrace_1708_ = lean_ctor_get_uint8(v_options_1706_, sizeof(void*)*1);
v___x_1709_ = lean_box(0);
v_a_1710_ = lean_array_uget_borrowed(v_as_1688_, v_i_1690_);
if (v_hasTrace_1708_ == 0)
{
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
v___y_1721_ = v___y_1701_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1737_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1738_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1707_, v_options_1706_, v___x_1738_);
if (v___x_1739_ == 0)
{
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
v___y_1721_ = v___y_1701_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Meta_Grind_updateLastTag(v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
v___x_1741_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1710_, v___y_1692_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1710_);
v___x_1744_ = l_Lean_MessageData_ofExpr(v_a_1710_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1742_);
lean_dec(v_a_1742_);
v___x_1749_ = lean_box(0);
v___x_1750_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1748_, v___x_1749_);
v___x_1751_ = l_Lean_MessageData_ofList(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1747_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1737_, v___x_1752_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_dec_ref_known(v___x_1753_, 1);
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
v___y_1721_ = v___y_1701_;
goto v___jp_1711_;
}
else
{
return v___x_1753_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1741_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1741_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
return v___x_1740_;
}
}
}
v___jp_1711_:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1710_, v___y_1712_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1723_);
lean_dec(v_a_1723_);
v___x_1725_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1686_, v_lams_1687_, v___x_1724_, v___x_1724_, v___x_1709_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___x_1724_);
if (lean_obj_tag(v___x_1725_) == 0)
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
lean_dec_ref_known(v___x_1725_, 1);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1690_, v___x_1726_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1686_, v_lams_1687_, v_as_1688_, v_sz_1689_, v___x_1727_, v___x_1709_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1728_;
}
else
{
return v___x_1725_;
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_a_1729_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1722_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1722_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1762_ = _args[0];
lean_object* v_lams_1763_ = _args[1];
lean_object* v_as_1764_ = _args[2];
lean_object* v_sz_1765_ = _args[3];
lean_object* v_i_1766_ = _args[4];
lean_object* v_b_1767_ = _args[5];
lean_object* v___y_1768_ = _args[6];
lean_object* v___y_1769_ = _args[7];
lean_object* v___y_1770_ = _args[8];
lean_object* v___y_1771_ = _args[9];
lean_object* v___y_1772_ = _args[10];
lean_object* v___y_1773_ = _args[11];
lean_object* v___y_1774_ = _args[12];
lean_object* v___y_1775_ = _args[13];
lean_object* v___y_1776_ = _args[14];
lean_object* v___y_1777_ = _args[15];
lean_object* v___y_1778_ = _args[16];
_start:
{
size_t v_sz_boxed_1779_; size_t v_i_boxed_1780_; lean_object* v_res_1781_; 
v_sz_boxed_1779_ = lean_unbox_usize(v_sz_1765_);
lean_dec(v_sz_1765_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1762_, v_lams_1763_, v_as_1764_, v_sz_boxed_1779_, v_i_boxed_1780_, v_b_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v_as_1764_);
lean_dec_ref(v_lams_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1788_, lean_object* v_fns_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_array_get_size(v_lams_1788_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_nat_dec_eq(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1804_ = lean_st_ref_get(v_a_1790_);
v___x_1805_ = l_Lean_instInhabitedExpr;
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_sub(v___x_1801_, v___x_1806_);
v___x_1808_ = lean_array_get_borrowed(v___x_1805_, v_lams_1788_, v___x_1807_);
lean_dec(v___x_1807_);
lean_inc(v___x_1808_);
v___x_1809_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1804_, v___x_1808_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v___x_1804_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v_toCold_1834_; lean_object* v_options_1835_; uint8_t v_hasTrace_1836_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v_toCold_1834_ = lean_ctor_get(v_a_1798_, 0);
v_options_1835_ = lean_ctor_get(v_toCold_1834_, 2);
v_hasTrace_1836_ = lean_ctor_get_uint8(v_options_1835_, sizeof(void*)*1);
if (v_hasTrace_1836_ == 0)
{
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
v___y_1821_ = v_a_1799_;
goto v___jp_1811_;
}
else
{
lean_object* v_inheritedTraceOptions_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_inheritedTraceOptions_1837_ = lean_ctor_get(v_toCold_1834_, 11);
v___x_1838_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1839_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1837_, v_options_1835_, v___x_1839_);
if (v___x_1840_ == 0)
{
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
v___y_1821_ = v_a_1799_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Meta_Grind_updateLastTag(v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref_known(v___x_1841_, 1);
v___x_1842_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1789_);
v___x_1843_ = lean_array_to_list(v_fns_1789_);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1843_, v___x_1844_);
v___x_1846_ = l_Lean_MessageData_ofList(v___x_1845_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1842_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
lean_inc_ref(v_lams_1788_);
v___x_1850_ = lean_array_to_list(v_lams_1788_);
v___x_1851_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1850_, v___x_1844_);
v___x_1852_ = l_Lean_MessageData_ofList(v___x_1851_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1849_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1838_, v___x_1853_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_dec_ref_known(v___x_1854_, 1);
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
v___y_1821_ = v_a_1799_;
goto v___jp_1811_;
}
else
{
lean_dec(v_a_1810_);
lean_dec_ref(v_fns_1789_);
lean_dec_ref(v_lams_1788_);
return v___x_1854_;
}
}
else
{
lean_dec(v_a_1810_);
lean_dec_ref(v_fns_1789_);
lean_dec_ref(v_lams_1788_);
return v___x_1841_;
}
}
}
v___jp_1811_:
{
lean_object* v___x_1822_; size_t v_sz_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1822_ = lean_box(0);
v_sz_1823_ = lean_array_size(v_fns_1789_);
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1810_, v_lams_1788_, v_fns_1789_, v_sz_1823_, v___x_1824_, v___x_1822_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec_ref(v_fns_1789_);
lean_dec_ref(v_lams_1788_);
lean_dec(v_a_1810_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v___x_1825_, 0);
lean_dec(v_unused_1833_);
v___x_1827_ = v___x_1825_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v___x_1825_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1822_);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1822_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_fns_1789_);
lean_dec_ref(v_lams_1788_);
v_a_1855_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1809_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1809_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_fns_1789_);
lean_dec_ref(v_lams_1788_);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1865_, lean_object* v_fns_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1865_, v_fns_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec(v_a_1867_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_lams_1881_, lean_object* v_inst_1882_, lean_object* v_a_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1879_, v_a_1880_, v_lams_1881_, v_a_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_lams_1898_, lean_object* v_inst_1899_, lean_object* v_a_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1896_, v_a_1897_, v_lams_1898_, v_inst_1899_, v_a_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v_lams_1898_);
lean_dec_ref(v_a_1897_);
lean_dec_ref(v_a_1896_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1913_, lean_object* v_lams_1914_, lean_object* v_as_1915_, lean_object* v_as_x27_1916_, lean_object* v_b_1917_, lean_object* v_a_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1913_, v_lams_1914_, v_as_1915_, v_as_x27_1916_, v_b_1917_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1931_ = _args[0];
lean_object* v_lams_1932_ = _args[1];
lean_object* v_as_1933_ = _args[2];
lean_object* v_as_x27_1934_ = _args[3];
lean_object* v_b_1935_ = _args[4];
lean_object* v_a_1936_ = _args[5];
lean_object* v___y_1937_ = _args[6];
lean_object* v___y_1938_ = _args[7];
lean_object* v___y_1939_ = _args[8];
lean_object* v___y_1940_ = _args[9];
lean_object* v___y_1941_ = _args[10];
lean_object* v___y_1942_ = _args[11];
lean_object* v___y_1943_ = _args[12];
lean_object* v___y_1944_ = _args[13];
lean_object* v___y_1945_ = _args[14];
lean_object* v___y_1946_ = _args[15];
lean_object* v___y_1947_ = _args[16];
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1931_, v_lams_1932_, v_as_1933_, v_as_x27_1934_, v_b_1935_, v_a_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec(v_as_x27_1934_);
lean_dec(v_as_1933_);
lean_dec_ref(v_lams_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1949_, lean_object* v_lams_1950_, lean_object* v_as_1951_, lean_object* v_as_x27_1952_, lean_object* v_b_1953_, lean_object* v_a_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1949_, v_lams_1950_, v_as_x27_1952_, v_b_1953_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1967_ = _args[0];
lean_object* v_lams_1968_ = _args[1];
lean_object* v_as_1969_ = _args[2];
lean_object* v_as_x27_1970_ = _args[3];
lean_object* v_b_1971_ = _args[4];
lean_object* v_a_1972_ = _args[5];
lean_object* v___y_1973_ = _args[6];
lean_object* v___y_1974_ = _args[7];
lean_object* v___y_1975_ = _args[8];
lean_object* v___y_1976_ = _args[9];
lean_object* v___y_1977_ = _args[10];
lean_object* v___y_1978_ = _args[11];
lean_object* v___y_1979_ = _args[12];
lean_object* v___y_1980_ = _args[13];
lean_object* v___y_1981_ = _args[14];
lean_object* v___y_1982_ = _args[15];
lean_object* v___y_1983_ = _args[16];
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1967_, v_lams_1968_, v_as_1969_, v_as_x27_1970_, v_b_1971_, v_a_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec(v_as_x27_1970_);
lean_dec(v_as_1969_);
lean_dec_ref(v_lams_1968_);
lean_dec_ref(v_a_1967_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1988_, lean_object* v_as_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_b_1992_){
_start:
{
lean_object* v_a_1994_; uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1998_ == 0)
{
lean_inc_ref(v_b_1992_);
return v_b_1992_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_a_2001_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_2001_ = lean_array_uget_borrowed(v_as_1989_, v_i_1991_);
if (lean_obj_tag(v_a_2001_) == 6)
{
lean_object* v_binderType_2002_; size_t v___x_2003_; size_t v___x_2004_; uint8_t v___x_2005_; 
v_binderType_2002_ = lean_ctor_get(v_a_2001_, 1);
v___x_2003_ = lean_ptr_addr(v_d_1988_);
v___x_2004_ = lean_ptr_addr(v_binderType_2002_);
v___x_2005_ = lean_usize_dec_eq(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
v_a_1994_ = v___x_2000_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_inc_ref(v_a_2001_);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_a_2001_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v___x_1999_);
return v___x_2008_;
}
}
else
{
v_a_1994_ = v___x_2000_;
goto v___jp_1993_;
}
}
v___jp_1993_:
{
size_t v___x_1995_; size_t v___x_1996_; 
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1991_, v___x_1995_);
v_i_1991_ = v___x_1996_;
v_b_1992_ = v_a_1994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2009_, lean_object* v_as_2010_, lean_object* v_sz_2011_, lean_object* v_i_2012_, lean_object* v_b_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2011_);
lean_dec(v_sz_2011_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2009_, v_as_2010_, v_sz_boxed_2014_, v_i_boxed_2015_, v_b_2013_);
lean_dec_ref(v_b_2013_);
lean_dec_ref(v_as_2010_);
lean_dec_ref(v_d_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2017_, lean_object* v_d_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; lean_object* v_fst_2024_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2021_ = lean_array_size(v_lams_2017_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2018_, v_lams_2017_, v_sz_2021_, v___x_2022_, v___x_2020_);
v_fst_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_fst_2024_);
lean_dec_ref(v___x_2023_);
if (lean_obj_tag(v_fst_2024_) == 0)
{
return v___x_2019_;
}
else
{
lean_object* v_val_2025_; 
v_val_2025_ = lean_ctor_get(v_fst_2024_, 0);
lean_inc(v_val_2025_);
lean_dec_ref_known(v_fst_2024_, 1);
return v_val_2025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2026_, lean_object* v_d_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2026_, v_d_2027_);
lean_dec_ref(v_d_2027_);
lean_dec_ref(v_lams_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2039_, lean_object* v_lams_u2081_2040_, lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_a_2057_; uint8_t v___x_2061_; 
v___x_2061_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_b_2044_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; lean_object* v_a_2064_; 
v___x_2063_ = lean_box(0);
v_a_2064_ = lean_array_uget_borrowed(v_as_2041_, v_i_2043_);
if (lean_obj_tag(v_a_2064_) == 6)
{
lean_object* v_binderType_2065_; lean_object* v_body_2066_; lean_object* v___x_2067_; 
v_binderType_2065_ = lean_ctor_get(v_a_2064_, 1);
v_body_2066_ = lean_ctor_get(v_a_2064_, 2);
lean_inc_ref(v_binderType_2065_);
v___x_2067_ = l_Lean_Meta_getLevel(v_binderType_2065_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_a_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
lean_inc_ref(v___x_2071_);
v___x_2072_ = l_Lean_mkConst(v___x_2069_, v___x_2071_);
lean_inc_ref(v_binderType_2065_);
v___x_2073_ = l_Lean_Expr_app___override(v___x_2072_, v_binderType_2065_);
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_Meta_synthInstance_x3f(v___x_2073_, v___x_2074_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
if (lean_obj_tag(v_a_2076_) == 1)
{
lean_object* v_val_2077_; lean_object* v___x_2078_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; uint8_t v___x_2143_; 
v_val_2077_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v_a_2076_, 1);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2143_ = l_Lean_Expr_hasLooseBVars(v_body_2066_);
if (v___x_2143_ == 0)
{
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
v___y_2086_ = v___y_2051_;
v___y_2087_ = v___y_2052_;
v___y_2088_ = v___y_2053_;
v___y_2089_ = v___y_2054_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2071_);
v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2071_);
lean_inc_ref(v_binderType_2065_);
v___x_2146_ = l_Lean_Expr_app___override(v___x_2145_, v_binderType_2065_);
v___x_2147_ = l_Lean_Meta_synthInstance_x3f(v___x_2146_, v___x_2074_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
if (lean_obj_tag(v_a_2148_) == 0)
{
lean_dec(v_val_2077_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
else
{
lean_dec_ref_known(v_a_2148_, 1);
if (v___x_2143_ == 0)
{
lean_dec(v_val_2077_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
else
{
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
v___y_2086_ = v___y_2051_;
v___y_2087_ = v___y_2052_;
v___y_2088_ = v___y_2053_;
v___y_2089_ = v___y_2054_;
goto v___jp_2079_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_val_2077_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2149_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2147_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2147_);
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
v___jp_2079_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2039_, v_binderType_2065_);
if (lean_obj_tag(v___x_2090_) == 1)
{
lean_object* v_val_2091_; 
v_val_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v___x_2090_, 1);
if (lean_obj_tag(v_val_2091_) == 6)
{
lean_object* v_binderType_2092_; lean_object* v_body_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_binderType_2092_ = lean_ctor_get(v_val_2091_, 1);
lean_inc_ref(v_binderType_2092_);
v_body_2093_ = lean_ctor_get(v_val_2091_, 2);
lean_inc_ref(v_body_2093_);
lean_dec_ref_known(v_val_2091_, 3);
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2095_ = l_Lean_mkConst(v___x_2094_, v___x_2071_);
v___x_2096_ = l_Lean_mkAppB(v___x_2095_, v_binderType_2092_, v_val_2077_);
v___x_2097_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2096_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = lean_array_fget_borrowed(v_lams_u2081_2040_, v___x_2078_);
v___x_2100_ = lean_array_fget_borrowed(v_lams_u2082_2039_, v___x_2078_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2088_);
lean_inc(v___y_2087_);
lean_inc_ref(v___y_2086_);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc(v___x_2100_);
lean_inc(v___x_2099_);
v___x_2101_ = lean_grind_mk_eq_proof(v___x_2099_, v___x_2100_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_expr_instantiate1(v_body_2066_, v_a_2098_);
v___x_2104_ = lean_expr_instantiate1(v_body_2093_, v_a_2098_);
lean_dec_ref(v_body_2093_);
v___x_2105_ = l_Lean_Meta_mkCongrFun(v_a_2102_, v_a_2098_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Meta_mkEq(v___x_2103_, v___x_2104_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Meta_mkExpectedPropHint(v_a_2106_, v_a_2108_);
v___x_2110_ = l_Lean_Meta_Grind_pushNewFact(v___x_2109_, v___x_2078_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref_known(v___x_2110_, 1);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
else
{
return v___x_2110_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2106_);
v_a_2111_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2107_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2107_);
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
lean_dec_ref(v___x_2104_);
lean_dec_ref(v___x_2103_);
v_a_2119_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2105_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2105_);
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
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_a_2098_);
lean_dec_ref(v_body_2093_);
v_a_2127_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2101_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2101_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_body_2093_);
v_a_2135_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2097_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2097_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_dec(v_val_2091_);
lean_dec(v_val_2077_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
}
else
{
lean_dec(v___x_2090_);
lean_dec(v_val_2077_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
}
}
else
{
lean_dec(v_a_2076_);
lean_dec_ref_known(v___x_2071_, 2);
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref_known(v___x_2071_, 2);
v_a_2157_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2075_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2075_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_a_2165_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2067_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2067_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
}
v___jp_2056_:
{
size_t v___x_2058_; size_t v___x_2059_; 
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2043_, v___x_2058_);
v_i_2043_ = v___x_2059_;
v_b_2044_ = v_a_2057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2173_ = _args[0];
lean_object* v_lams_u2081_2174_ = _args[1];
lean_object* v_as_2175_ = _args[2];
lean_object* v_sz_2176_ = _args[3];
lean_object* v_i_2177_ = _args[4];
lean_object* v_b_2178_ = _args[5];
lean_object* v___y_2179_ = _args[6];
lean_object* v___y_2180_ = _args[7];
lean_object* v___y_2181_ = _args[8];
lean_object* v___y_2182_ = _args[9];
lean_object* v___y_2183_ = _args[10];
lean_object* v___y_2184_ = _args[11];
lean_object* v___y_2185_ = _args[12];
lean_object* v___y_2186_ = _args[13];
lean_object* v___y_2187_ = _args[14];
lean_object* v___y_2188_ = _args[15];
lean_object* v___y_2189_ = _args[16];
_start:
{
size_t v_sz_boxed_2190_; size_t v_i_boxed_2191_; lean_object* v_res_2192_; 
v_sz_boxed_2190_ = lean_unbox_usize(v_sz_2176_);
lean_dec(v_sz_2176_);
v_i_boxed_2191_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2173_, v_lams_u2081_2174_, v_as_2175_, v_sz_boxed_2190_, v_i_boxed_2191_, v_b_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v_as_2175_);
lean_dec_ref(v_lams_u2081_2174_);
lean_dec_ref(v_lams_u2082_2173_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2193_, lean_object* v_lams_u2082_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_array_get_size(v_lams_u2081_2193_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = lean_nat_dec_eq(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_array_get_size(v_lams_u2082_2194_);
v___x_2210_ = lean_nat_dec_eq(v___x_2209_, v___x_2207_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; size_t v_sz_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = lean_box(0);
v_sz_2212_ = lean_array_size(v_lams_u2081_2193_);
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2194_, v_lams_u2081_2193_, v_lams_u2081_2193_, v_sz_2212_, v___x_2213_, v___x_2211_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v___x_2214_, 0);
lean_dec(v_unused_2222_);
v___x_2216_ = v___x_2214_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_dec(v___x_2214_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2211_);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2211_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
return v___x_2214_;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2227_, lean_object* v_lams_u2082_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2227_, v_lams_u2082_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_lams_u2082_2228_);
lean_dec_ref(v_lams_u2081_2227_);
return v_res_2240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2243_);
lean_dec_ref(v_x_2243_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2246_, lean_object* v_x_2247_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2249_, lean_object* v_x_2250_){
_start:
{
uint8_t v_res_2251_; lean_object* v_r_2252_; 
v_res_2251_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2249_, v_x_2250_);
lean_dec_ref(v_x_2250_);
v_r_2252_ = lean_box(v_res_2251_);
return v_r_2252_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2253_, lean_object* v_v_2254_, lean_object* v_i_2255_){
_start:
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_array_get_size(v_xs_2253_);
v___x_2257_ = lean_nat_dec_lt(v_i_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_dec(v_i_2255_);
v___x_2258_ = lean_box(0);
return v___x_2258_;
}
else
{
lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2259_ = lean_array_fget_borrowed(v_xs_2253_, v_i_2255_);
v___x_2260_ = lean_ptr_addr(v___x_2259_);
v___x_2261_ = lean_ptr_addr(v_v_2254_);
v___x_2262_ = lean_usize_dec_eq(v___x_2260_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_add(v_i_2255_, v___x_2263_);
lean_dec(v_i_2255_);
v_i_2255_ = v___x_2264_;
goto _start;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_i_2255_);
return v___x_2266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2267_, lean_object* v_v_2268_, lean_object* v_i_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2267_, v_v_2268_, v_i_2269_);
lean_dec_ref(v_v_2268_);
lean_dec_ref(v_xs_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2271_, lean_object* v_v_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2271_, v_v_2272_, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2275_, lean_object* v_v_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2275_, v_v_2276_);
lean_dec_ref(v_v_2276_);
lean_dec_ref(v_xs_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2278_, size_t v_x_2279_, lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2278_) == 0)
{
lean_object* v_es_2281_; lean_object* v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v_j_2285_; lean_object* v_entry_2286_; 
v_es_2281_ = lean_ctor_get(v_x_2278_, 0);
v___x_2282_ = lean_box(2);
v___x_2283_ = ((size_t)31ULL);
v___x_2284_ = lean_usize_land(v_x_2279_, v___x_2283_);
v_j_2285_ = lean_usize_to_nat(v___x_2284_);
v_entry_2286_ = lean_array_get(v___x_2282_, v_es_2281_, v_j_2285_);
switch(lean_obj_tag(v_entry_2286_))
{
case 0:
{
lean_object* v_key_2287_; size_t v___x_2288_; size_t v___x_2289_; uint8_t v___x_2290_; 
v_key_2287_ = lean_ctor_get(v_entry_2286_, 0);
lean_inc(v_key_2287_);
lean_dec_ref_known(v_entry_2286_, 2);
v___x_2288_ = lean_ptr_addr(v_x_2280_);
v___x_2289_ = lean_ptr_addr(v_key_2287_);
lean_dec(v_key_2287_);
v___x_2290_ = lean_usize_dec_eq(v___x_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_j_2285_);
return v_x_2278_;
}
else
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2298_; 
lean_inc_ref(v_es_2281_);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_x_2278_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v_x_2278_, 0);
lean_dec(v_unused_2299_);
v___x_2292_ = v_x_2278_;
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_x_2278_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_array_set(v_es_2281_, v_j_2285_, v___x_2282_);
lean_dec(v_j_2285_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2294_);
v___x_2296_ = v___x_2292_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
case 1:
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2334_; 
lean_inc_ref(v_es_2281_);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2278_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v_x_2278_, 0);
lean_dec(v_unused_2335_);
v___x_2301_ = v_x_2278_;
v_isShared_2302_ = v_isSharedCheck_2334_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v_x_2278_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2334_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_node_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2333_; 
v_node_2303_ = lean_ctor_get(v_entry_2286_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_entry_2286_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2305_ = v_entry_2286_;
v_isShared_2306_ = v_isSharedCheck_2333_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_node_2303_);
lean_dec(v_entry_2286_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2333_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
size_t v___x_2307_; lean_object* v_entries_2308_; size_t v___x_2309_; lean_object* v_newNode_2310_; lean_object* v___x_2311_; 
v___x_2307_ = ((size_t)5ULL);
v_entries_2308_ = lean_array_set(v_es_2281_, v_j_2285_, v___x_2282_);
v___x_2309_ = lean_usize_shift_right(v_x_2279_, v___x_2307_);
v_newNode_2310_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2303_, v___x_2309_, v_x_2280_);
lean_inc_ref(v_newNode_2310_);
v___x_2311_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2310_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v___x_2313_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_newNode_2310_);
v___x_2313_ = v___x_2305_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_newNode_2310_);
v___x_2313_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_array_set(v_entries_2308_, v_j_2285_, v___x_2313_);
lean_dec(v_j_2285_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2314_);
v___x_2316_ = v___x_2301_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
else
{
lean_object* v_val_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_newNode_2310_);
lean_del_object(v___x_2305_);
v_val_2319_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_val_2319_);
lean_dec_ref_known(v___x_2311_, 1);
v_fst_2320_ = lean_ctor_get(v_val_2319_, 0);
v_snd_2321_ = lean_ctor_get(v_val_2319_, 1);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_val_2319_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2323_ = v_val_2319_;
v_isShared_2324_ = v_isSharedCheck_2332_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_snd_2321_);
lean_inc(v_fst_2320_);
lean_dec(v_val_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2332_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2320_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_snd_2321_);
v___x_2326_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_array_set(v_entries_2308_, v_j_2285_, v___x_2326_);
lean_dec(v_j_2285_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2327_);
v___x_2329_ = v___x_2301_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2285_);
return v_x_2278_;
}
}
}
else
{
lean_object* v_ks_2336_; lean_object* v_vs_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2351_; 
v_ks_2336_ = lean_ctor_get(v_x_2278_, 0);
v_vs_2337_ = lean_ctor_get(v_x_2278_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2278_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2339_ = v_x_2278_;
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_vs_2337_);
lean_inc(v_ks_2336_);
lean_dec(v_x_2278_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2351_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2336_, v_x_2280_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2343_; 
if (v_isShared_2340_ == 0)
{
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_ks_2336_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_vs_2337_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
else
{
lean_object* v_val_2345_; lean_object* v_keys_x27_2346_; lean_object* v_vals_x27_2347_; lean_object* v___x_2349_; 
v_val_2345_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_n(v_val_2345_, 2);
lean_dec_ref_known(v___x_2341_, 1);
v_keys_x27_2346_ = l_Array_eraseIdx___redArg(v_ks_2336_, v_val_2345_);
v_vals_x27_2347_ = l_Array_eraseIdx___redArg(v_vs_2337_, v_val_2345_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v_vals_x27_2347_);
lean_ctor_set(v___x_2339_, 0, v_keys_x27_2346_);
v___x_2349_ = v___x_2339_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_keys_x27_2346_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_vals_x27_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
size_t v_x_19384__boxed_2355_; lean_object* v_res_2356_; 
v_x_19384__boxed_2355_ = lean_unbox_usize(v_x_2353_);
lean_dec(v_x_2353_);
v_res_2356_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2352_, v_x_19384__boxed_2355_, v_x_2354_);
lean_dec_ref(v_x_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2357_, lean_object* v_x_2358_){
_start:
{
size_t v___x_2359_; size_t v___x_2360_; size_t v___x_2361_; uint64_t v___x_2362_; size_t v_h_2363_; lean_object* v___x_2364_; 
v___x_2359_ = lean_ptr_addr(v_x_2358_);
v___x_2360_ = ((size_t)3ULL);
v___x_2361_ = lean_usize_shift_right(v___x_2359_, v___x_2360_);
v___x_2362_ = lean_usize_to_uint64(v___x_2361_);
v_h_2363_ = lean_uint64_to_usize(v___x_2362_);
v___x_2364_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2357_, v_h_2363_, v_x_2358_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2365_, v_x_2366_);
lean_dec_ref(v_x_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
if (lean_obj_tag(v_as_2368_) == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
else
{
lean_object* v_head_2382_; lean_object* v_tail_2383_; lean_object* v___x_2384_; 
v_head_2382_ = lean_ctor_get(v_as_2368_, 0);
lean_inc(v_head_2382_);
v_tail_2383_ = lean_ctor_get(v_as_2368_, 1);
lean_inc(v_tail_2383_);
lean_dec_ref_known(v_as_2368_, 2);
v___x_2384_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2382_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_dec_ref_known(v___x_2384_, 1);
v_as_2368_ = v_tail_2383_;
goto _start;
}
else
{
lean_dec(v_tail_2383_);
return v___x_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec(v___y_2387_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2399_, lean_object* v_vals_2400_, lean_object* v_i_2401_, lean_object* v_k_2402_){
_start:
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = lean_array_get_size(v_keys_2399_);
v___x_2404_ = lean_nat_dec_lt(v_i_2401_, v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
lean_dec(v_i_2401_);
v___x_2405_ = lean_box(0);
return v___x_2405_;
}
else
{
lean_object* v_k_x27_2406_; size_t v___x_2407_; size_t v___x_2408_; uint8_t v___x_2409_; 
v_k_x27_2406_ = lean_array_fget_borrowed(v_keys_2399_, v_i_2401_);
v___x_2407_ = lean_ptr_addr(v_k_2402_);
v___x_2408_ = lean_ptr_addr(v_k_x27_2406_);
v___x_2409_ = lean_usize_dec_eq(v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_add(v_i_2401_, v___x_2410_);
lean_dec(v_i_2401_);
v_i_2401_ = v___x_2411_;
goto _start;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_array_fget_borrowed(v_vals_2400_, v_i_2401_);
lean_dec(v_i_2401_);
lean_inc(v___x_2413_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2415_, lean_object* v_vals_2416_, lean_object* v_i_2417_, lean_object* v_k_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2415_, v_vals_2416_, v_i_2417_, v_k_2418_);
lean_dec_ref(v_k_2418_);
lean_dec_ref(v_vals_2416_);
lean_dec_ref(v_keys_2415_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2420_, size_t v_x_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2420_) == 0)
{
lean_object* v_es_2423_; lean_object* v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; lean_object* v_j_2427_; lean_object* v___x_2428_; 
v_es_2423_ = lean_ctor_get(v_x_2420_, 0);
v___x_2424_ = lean_box(2);
v___x_2425_ = ((size_t)31ULL);
v___x_2426_ = lean_usize_land(v_x_2421_, v___x_2425_);
v_j_2427_ = lean_usize_to_nat(v___x_2426_);
v___x_2428_ = lean_array_get_borrowed(v___x_2424_, v_es_2423_, v_j_2427_);
lean_dec(v_j_2427_);
switch(lean_obj_tag(v___x_2428_))
{
case 0:
{
lean_object* v_key_2429_; lean_object* v_val_2430_; size_t v___x_2431_; size_t v___x_2432_; uint8_t v___x_2433_; 
v_key_2429_ = lean_ctor_get(v___x_2428_, 0);
v_val_2430_ = lean_ctor_get(v___x_2428_, 1);
v___x_2431_ = lean_ptr_addr(v_x_2422_);
v___x_2432_ = lean_ptr_addr(v_key_2429_);
v___x_2433_ = lean_usize_dec_eq(v___x_2431_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_box(0);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; 
lean_inc(v_val_2430_);
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v_val_2430_);
return v___x_2435_;
}
}
case 1:
{
lean_object* v_node_2436_; size_t v___x_2437_; size_t v___x_2438_; 
v_node_2436_ = lean_ctor_get(v___x_2428_, 0);
v___x_2437_ = ((size_t)5ULL);
v___x_2438_ = lean_usize_shift_right(v_x_2421_, v___x_2437_);
v_x_2420_ = v_node_2436_;
v_x_2421_ = v___x_2438_;
goto _start;
}
default: 
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_box(0);
return v___x_2440_;
}
}
}
else
{
lean_object* v_ks_2441_; lean_object* v_vs_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_ks_2441_ = lean_ctor_get(v_x_2420_, 0);
v_vs_2442_ = lean_ctor_get(v_x_2420_, 1);
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2444_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2441_, v_vs_2442_, v___x_2443_, v_x_2422_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
size_t v_x_19609__boxed_2448_; lean_object* v_res_2449_; 
v_x_19609__boxed_2448_ = lean_unbox_usize(v_x_2446_);
lean_dec(v_x_2446_);
v_res_2449_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2445_, v_x_19609__boxed_2448_, v_x_2447_);
lean_dec_ref(v_x_2447_);
lean_dec_ref(v_x_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
size_t v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; uint64_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2452_ = lean_ptr_addr(v_x_2451_);
v___x_2453_ = ((size_t)3ULL);
v___x_2454_ = lean_usize_shift_right(v___x_2452_, v___x_2453_);
v___x_2455_ = lean_usize_to_uint64(v___x_2454_);
v___x_2456_ = lean_uint64_to_usize(v___x_2455_);
v___x_2457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2450_, v___x_2456_, v_x_2451_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2458_, v_x_2459_);
lean_dec_ref(v_x_2459_);
lean_dec_ref(v_x_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2461_, lean_object* v_b_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
if (lean_obj_tag(v_as_x27_2461_) == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2462_);
return v___x_2474_;
}
else
{
lean_object* v_head_2475_; lean_object* v_tail_2476_; lean_object* v___x_2477_; lean_object* v_toGoalState_2478_; lean_object* v_ematch_2479_; lean_object* v_delayedThmInsts_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_head_2475_ = lean_ctor_get(v_as_x27_2461_, 0);
v_tail_2476_ = lean_ctor_get(v_as_x27_2461_, 1);
v___x_2477_ = lean_st_ref_get(v___y_2463_);
v_toGoalState_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_toGoalState_2478_);
lean_dec(v___x_2477_);
v_ematch_2479_ = lean_ctor_get(v_toGoalState_2478_, 12);
lean_inc_ref(v_ematch_2479_);
lean_dec_ref(v_toGoalState_2478_);
v_delayedThmInsts_2480_ = lean_ctor_get(v_ematch_2479_, 10);
lean_inc_ref(v_delayedThmInsts_2480_);
lean_dec_ref(v_ematch_2479_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2480_, v_head_2475_);
lean_dec_ref(v_delayedThmInsts_2480_);
if (lean_obj_tag(v___x_2482_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v_toGoalState_2485_; lean_object* v_ematch_2486_; lean_object* v_mvarId_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2541_; 
v_val_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = lean_st_ref_take(v___y_2463_);
v_toGoalState_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc_ref(v_toGoalState_2485_);
v_ematch_2486_ = lean_ctor_get(v_toGoalState_2485_, 12);
lean_inc_ref(v_ematch_2486_);
v_mvarId_2487_ = lean_ctor_get(v___x_2484_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v___x_2484_, 0);
lean_dec(v_unused_2542_);
v___x_2489_ = v___x_2484_;
v_isShared_2490_ = v_isSharedCheck_2541_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_mvarId_2487_);
lean_dec(v___x_2484_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2541_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_nextDeclIdx_2491_; lean_object* v_enodeMap_2492_; lean_object* v_exprs_2493_; lean_object* v_parents_2494_; lean_object* v_congrTable_2495_; lean_object* v_appMap_2496_; lean_object* v_indicesFound_2497_; lean_object* v_newFacts_2498_; uint8_t v_inconsistent_2499_; lean_object* v_nextIdx_2500_; lean_object* v_newRawFacts_2501_; lean_object* v_facts_2502_; lean_object* v_extThms_2503_; lean_object* v_inj_2504_; lean_object* v_split_2505_; lean_object* v_clean_2506_; lean_object* v_sstates_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2539_; 
v_nextDeclIdx_2491_ = lean_ctor_get(v_toGoalState_2485_, 0);
v_enodeMap_2492_ = lean_ctor_get(v_toGoalState_2485_, 1);
v_exprs_2493_ = lean_ctor_get(v_toGoalState_2485_, 2);
v_parents_2494_ = lean_ctor_get(v_toGoalState_2485_, 3);
v_congrTable_2495_ = lean_ctor_get(v_toGoalState_2485_, 4);
v_appMap_2496_ = lean_ctor_get(v_toGoalState_2485_, 5);
v_indicesFound_2497_ = lean_ctor_get(v_toGoalState_2485_, 6);
v_newFacts_2498_ = lean_ctor_get(v_toGoalState_2485_, 7);
v_inconsistent_2499_ = lean_ctor_get_uint8(v_toGoalState_2485_, sizeof(void*)*17);
v_nextIdx_2500_ = lean_ctor_get(v_toGoalState_2485_, 8);
v_newRawFacts_2501_ = lean_ctor_get(v_toGoalState_2485_, 9);
v_facts_2502_ = lean_ctor_get(v_toGoalState_2485_, 10);
v_extThms_2503_ = lean_ctor_get(v_toGoalState_2485_, 11);
v_inj_2504_ = lean_ctor_get(v_toGoalState_2485_, 13);
v_split_2505_ = lean_ctor_get(v_toGoalState_2485_, 14);
v_clean_2506_ = lean_ctor_get(v_toGoalState_2485_, 15);
v_sstates_2507_ = lean_ctor_get(v_toGoalState_2485_, 16);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_toGoalState_2485_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v_toGoalState_2485_, 12);
lean_dec(v_unused_2540_);
v___x_2509_ = v_toGoalState_2485_;
v_isShared_2510_ = v_isSharedCheck_2539_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_sstates_2507_);
lean_inc(v_clean_2506_);
lean_inc(v_split_2505_);
lean_inc(v_inj_2504_);
lean_inc(v_extThms_2503_);
lean_inc(v_facts_2502_);
lean_inc(v_newRawFacts_2501_);
lean_inc(v_nextIdx_2500_);
lean_inc(v_newFacts_2498_);
lean_inc(v_indicesFound_2497_);
lean_inc(v_appMap_2496_);
lean_inc(v_congrTable_2495_);
lean_inc(v_parents_2494_);
lean_inc(v_exprs_2493_);
lean_inc(v_enodeMap_2492_);
lean_inc(v_nextDeclIdx_2491_);
lean_dec(v_toGoalState_2485_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2539_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_thmMap_2511_; lean_object* v_gmt_2512_; lean_object* v_thms_2513_; lean_object* v_newThms_2514_; lean_object* v_numInstances_2515_; lean_object* v_numDelayedInstances_2516_; lean_object* v_num_2517_; lean_object* v_preInstances_2518_; lean_object* v_nextThmIdx_2519_; lean_object* v_matchEqNames_2520_; lean_object* v_delayedThmInsts_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2538_; 
v_thmMap_2511_ = lean_ctor_get(v_ematch_2486_, 0);
v_gmt_2512_ = lean_ctor_get(v_ematch_2486_, 1);
v_thms_2513_ = lean_ctor_get(v_ematch_2486_, 2);
v_newThms_2514_ = lean_ctor_get(v_ematch_2486_, 3);
v_numInstances_2515_ = lean_ctor_get(v_ematch_2486_, 4);
v_numDelayedInstances_2516_ = lean_ctor_get(v_ematch_2486_, 5);
v_num_2517_ = lean_ctor_get(v_ematch_2486_, 6);
v_preInstances_2518_ = lean_ctor_get(v_ematch_2486_, 7);
v_nextThmIdx_2519_ = lean_ctor_get(v_ematch_2486_, 8);
v_matchEqNames_2520_ = lean_ctor_get(v_ematch_2486_, 9);
v_delayedThmInsts_2521_ = lean_ctor_get(v_ematch_2486_, 10);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_ematch_2486_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2523_ = v_ematch_2486_;
v_isShared_2524_ = v_isSharedCheck_2538_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_delayedThmInsts_2521_);
lean_inc(v_matchEqNames_2520_);
lean_inc(v_nextThmIdx_2519_);
lean_inc(v_preInstances_2518_);
lean_inc(v_num_2517_);
lean_inc(v_numDelayedInstances_2516_);
lean_inc(v_numInstances_2515_);
lean_inc(v_newThms_2514_);
lean_inc(v_thms_2513_);
lean_inc(v_gmt_2512_);
lean_inc(v_thmMap_2511_);
lean_dec(v_ematch_2486_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2538_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2521_, v_head_2475_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 10, v___x_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_thmMap_2511_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_gmt_2512_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_thms_2513_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_newThms_2514_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_numInstances_2515_);
lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_numDelayedInstances_2516_);
lean_ctor_set(v_reuseFailAlloc_2537_, 6, v_num_2517_);
lean_ctor_set(v_reuseFailAlloc_2537_, 7, v_preInstances_2518_);
lean_ctor_set(v_reuseFailAlloc_2537_, 8, v_nextThmIdx_2519_);
lean_ctor_set(v_reuseFailAlloc_2537_, 9, v_matchEqNames_2520_);
lean_ctor_set(v_reuseFailAlloc_2537_, 10, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 12, v___x_2527_);
v___x_2529_ = v___x_2509_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_nextDeclIdx_2491_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_enodeMap_2492_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_exprs_2493_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_parents_2494_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_congrTable_2495_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_appMap_2496_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_indicesFound_2497_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_newFacts_2498_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_nextIdx_2500_);
lean_ctor_set(v_reuseFailAlloc_2536_, 9, v_newRawFacts_2501_);
lean_ctor_set(v_reuseFailAlloc_2536_, 10, v_facts_2502_);
lean_ctor_set(v_reuseFailAlloc_2536_, 11, v_extThms_2503_);
lean_ctor_set(v_reuseFailAlloc_2536_, 12, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2536_, 13, v_inj_2504_);
lean_ctor_set(v_reuseFailAlloc_2536_, 14, v_split_2505_);
lean_ctor_set(v_reuseFailAlloc_2536_, 15, v_clean_2506_);
lean_ctor_set(v_reuseFailAlloc_2536_, 16, v_sstates_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2536_, sizeof(void*)*17, v_inconsistent_2499_);
v___x_2529_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2529_);
v___x_2531_ = v___x_2489_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_mvarId_2487_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_st_ref_put(v___y_2463_, v___x_2531_);
v___x_2533_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2483_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
v_as_x27_2461_ = v_tail_2476_;
v_b_2462_ = v___x_2481_;
goto _start;
}
else
{
return v___x_2533_;
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
lean_dec(v___x_2482_);
v_as_x27_2461_ = v_tail_2476_;
v_b_2462_ = v___x_2481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2544_, v_b_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec(v_as_x27_2544_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2559_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2599_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2599_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2599_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
uint8_t v___x_2575_; 
v___x_2575_ = lean_unbox(v_a_2571_);
lean_dec(v_a_2571_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v_toGoalState_2577_; lean_object* v_ematch_2578_; lean_object* v_delayedThmInsts_2579_; uint8_t v___x_2580_; 
v___x_2576_ = lean_st_ref_get(v_a_2559_);
v_toGoalState_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc_ref(v_toGoalState_2577_);
lean_dec(v___x_2576_);
v_ematch_2578_ = lean_ctor_get(v_toGoalState_2577_, 12);
lean_inc_ref(v_ematch_2578_);
lean_dec_ref(v_toGoalState_2577_);
v_delayedThmInsts_2579_ = lean_ctor_get(v_ematch_2578_, 10);
lean_inc_ref(v_delayedThmInsts_2579_);
lean_dec_ref(v_ematch_2578_);
v___x_2580_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2579_);
lean_dec_ref(v_delayedThmInsts_2579_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_del_object(v___x_2573_);
v___x_2581_ = lean_box(0);
v___x_2582_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2558_, v___x_2581_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v___x_2582_, 0);
lean_dec(v_unused_2590_);
v___x_2584_ = v___x_2582_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_dec(v___x_2582_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2581_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2581_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
return v___x_2582_;
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2591_);
v___x_2593_ = v___x_2573_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2595_);
v___x_2597_ = v___x_2573_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_a_2600_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2570_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2570_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec(v_toPropagateDown_2608_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2622_, v_x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2625_, v_x_2626_, v_x_2627_);
lean_dec_ref(v_x_2627_);
lean_dec_ref(v_x_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2630_, v_x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2633_, lean_object* v_x_2634_, lean_object* v_x_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2633_, v_x_2634_, v_x_2635_);
lean_dec_ref(v_x_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2637_, lean_object* v_as_x27_2638_, lean_object* v_b_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2638_, v_b_2639_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2653_, lean_object* v_as_x27_2654_, lean_object* v_b_2655_, lean_object* v_a_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2653_, v_as_x27_2654_, v_b_2655_, v_a_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v_as_x27_2654_);
lean_dec(v_as_2653_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, size_t v_x_2671_, lean_object* v_x_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2670_, v_x_2671_, v_x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
size_t v_x_19914__boxed_2678_; lean_object* v_res_2679_; 
v_x_19914__boxed_2678_ = lean_unbox_usize(v_x_2676_);
lean_dec(v_x_2676_);
v_res_2679_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2674_, v_x_2675_, v_x_19914__boxed_2678_, v_x_2677_);
lean_dec_ref(v_x_2677_);
lean_dec_ref(v_x_2675_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2680_, lean_object* v_x_2681_, size_t v_x_2682_, lean_object* v_x_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2681_, v_x_2682_, v_x_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
size_t v_x_19925__boxed_2689_; lean_object* v_res_2690_; 
v_x_19925__boxed_2689_ = lean_unbox_usize(v_x_2687_);
lean_dec(v_x_2687_);
v_res_2690_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2685_, v_x_2686_, v_x_19925__boxed_2689_, v_x_2688_);
lean_dec_ref(v_x_2688_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2691_, lean_object* v_keys_2692_, lean_object* v_vals_2693_, lean_object* v_heq_2694_, lean_object* v_i_2695_, lean_object* v_k_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2692_, v_vals_2693_, v_i_2695_, v_k_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2698_, lean_object* v_keys_2699_, lean_object* v_vals_2700_, lean_object* v_heq_2701_, lean_object* v_i_2702_, lean_object* v_k_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2698_, v_keys_2699_, v_vals_2700_, v_heq_2701_, v_i_2702_, v_k_2703_);
lean_dec_ref(v_k_2703_);
lean_dec_ref(v_vals_2700_);
lean_dec_ref(v_keys_2699_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2705_, lean_object* v_keys_2706_, lean_object* v_vals_2707_, lean_object* v_i_2708_, lean_object* v_k_2709_){
_start:
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = lean_array_get_size(v_keys_2706_);
v___x_2711_ = lean_nat_dec_lt(v_i_2708_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
lean_dec_ref(v_k_2709_);
lean_dec(v_i_2708_);
v___x_2712_ = lean_box(0);
return v___x_2712_;
}
else
{
lean_object* v_k_x27_2713_; uint8_t v___x_2714_; 
v_k_x27_2713_ = lean_array_fget_borrowed(v_keys_2706_, v_i_2708_);
lean_inc(v_k_x27_2713_);
lean_inc_ref(v_k_2709_);
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2705_, v_k_2709_, v_k_x27_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_add(v_i_2708_, v___x_2715_);
lean_dec(v_i_2708_);
v_i_2708_ = v___x_2716_;
goto _start;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v_k_2709_);
v___x_2718_ = lean_array_fget_borrowed(v_vals_2707_, v_i_2708_);
lean_dec(v_i_2708_);
lean_inc(v___x_2718_);
lean_inc(v_k_x27_2713_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_k_x27_2713_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2721_, lean_object* v_keys_2722_, lean_object* v_vals_2723_, lean_object* v_i_2724_, lean_object* v_k_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2721_, v_keys_2722_, v_vals_2723_, v_i_2724_, v_k_2725_);
lean_dec_ref(v_vals_2723_);
lean_dec_ref(v_keys_2722_);
lean_dec_ref(v___x_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2727_, lean_object* v_x_2728_, size_t v_x_2729_, lean_object* v_x_2730_){
_start:
{
if (lean_obj_tag(v_x_2728_) == 0)
{
lean_object* v_es_2731_; lean_object* v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v_j_2735_; lean_object* v___x_2736_; 
v_es_2731_ = lean_ctor_get(v_x_2728_, 0);
lean_inc_ref(v_es_2731_);
lean_dec_ref_known(v_x_2728_, 1);
v___x_2732_ = lean_box(2);
v___x_2733_ = ((size_t)31ULL);
v___x_2734_ = lean_usize_land(v_x_2729_, v___x_2733_);
v_j_2735_ = lean_usize_to_nat(v___x_2734_);
v___x_2736_ = lean_array_get(v___x_2732_, v_es_2731_, v_j_2735_);
lean_dec(v_j_2735_);
lean_dec_ref(v_es_2731_);
switch(lean_obj_tag(v___x_2736_))
{
case 0:
{
lean_object* v_key_2737_; lean_object* v_val_2738_; uint8_t v___x_2739_; 
v_key_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_n(v_key_2737_, 2);
v_val_2738_ = lean_ctor_get(v___x_2736_, 1);
lean_inc(v_val_2738_);
lean_dec_ref_known(v___x_2736_, 2);
v___x_2739_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2727_, v_x_2730_, v_key_2737_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_dec(v_val_2738_);
lean_dec(v_key_2737_);
v___x_2740_ = lean_box(0);
return v___x_2740_;
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_key_2737_);
lean_ctor_set(v___x_2741_, 1, v_val_2738_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
return v___x_2742_;
}
}
case 1:
{
lean_object* v_node_2743_; size_t v___x_2744_; size_t v___x_2745_; 
v_node_2743_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_node_2743_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2744_ = ((size_t)5ULL);
v___x_2745_ = lean_usize_shift_right(v_x_2729_, v___x_2744_);
v_x_2728_ = v_node_2743_;
v_x_2729_ = v___x_2745_;
goto _start;
}
default: 
{
lean_object* v___x_2747_; 
lean_dec_ref(v_x_2730_);
v___x_2747_ = lean_box(0);
return v___x_2747_;
}
}
}
else
{
lean_object* v_ks_2748_; lean_object* v_vs_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_ks_2748_ = lean_ctor_get(v_x_2728_, 0);
lean_inc_ref(v_ks_2748_);
v_vs_2749_ = lean_ctor_get(v_x_2728_, 1);
lean_inc_ref(v_vs_2749_);
lean_dec_ref_known(v_x_2728_, 2);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2727_, v_ks_2748_, v_vs_2749_, v___x_2750_, v_x_2730_);
lean_dec_ref(v_vs_2749_);
lean_dec_ref(v_ks_2748_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
size_t v_x_25943__boxed_2756_; lean_object* v_res_2757_; 
v_x_25943__boxed_2756_ = lean_unbox_usize(v_x_2754_);
lean_dec(v_x_2754_);
v_res_2757_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2752_, v_x_2753_, v_x_25943__boxed_2756_, v_x_2755_);
lean_dec_ref(v___x_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2758_, lean_object* v_x_2759_, lean_object* v_x_2760_){
_start:
{
uint64_t v___x_2761_; size_t v___x_2762_; lean_object* v___x_2763_; 
lean_inc_ref(v_x_2760_);
v___x_2761_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2758_, v_x_2760_);
v___x_2762_ = lean_uint64_to_usize(v___x_2761_);
lean_inc_ref(v_x_2759_);
v___x_2763_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2758_, v_x_2759_, v___x_2762_, v_x_2760_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2764_, v_x_2765_, v_x_2766_);
lean_dec_ref(v_x_2765_);
lean_dec_ref(v___x_2764_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v_ks_2773_; lean_object* v_vs_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2798_; 
v_ks_2773_ = lean_ctor_get(v_x_2769_, 0);
v_vs_2774_ = lean_ctor_get(v_x_2769_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_x_2769_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2776_ = v_x_2769_;
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_vs_2774_);
lean_inc(v_ks_2773_);
lean_dec(v_x_2769_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = lean_array_get_size(v_ks_2773_);
v___x_2779_ = lean_nat_dec_lt(v_x_2770_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
lean_dec(v_x_2770_);
v___x_2780_ = lean_array_push(v_ks_2773_, v_x_2771_);
v___x_2781_ = lean_array_push(v_vs_2774_, v_x_2772_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2781_);
lean_ctor_set(v___x_2776_, 0, v___x_2780_);
v___x_2783_ = v___x_2776_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
else
{
lean_object* v_k_x27_2785_; uint8_t v___x_2786_; 
v_k_x27_2785_ = lean_array_fget_borrowed(v_ks_2773_, v_x_2770_);
lean_inc(v_k_x27_2785_);
lean_inc_ref(v_x_2771_);
v___x_2786_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2768_, v_x_2771_, v_k_x27_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2788_; 
if (v_isShared_2777_ == 0)
{
v___x_2788_ = v___x_2776_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_ks_2773_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_vs_2774_);
v___x_2788_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v_x_2770_, v___x_2789_);
lean_dec(v_x_2770_);
v_x_2769_ = v___x_2788_;
v_x_2770_ = v___x_2790_;
goto _start;
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_array_fset(v_ks_2773_, v_x_2770_, v_x_2771_);
v___x_2794_ = lean_array_fset(v_vs_2774_, v_x_2770_, v_x_2772_);
lean_dec(v_x_2770_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2794_);
lean_ctor_set(v___x_2776_, 0, v___x_2793_);
v___x_2796_ = v___x_2776_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2799_, v_x_2800_, v_x_2801_, v_x_2802_, v_x_2803_);
lean_dec_ref(v___x_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2805_, lean_object* v_n_2806_, lean_object* v_k_2807_, lean_object* v_v_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2805_, v_n_2806_, v___x_2809_, v_k_2807_, v_v_2808_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2811_, lean_object* v_n_2812_, lean_object* v_k_2813_, lean_object* v_v_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2811_, v_n_2812_, v_k_2813_, v_v_2814_);
lean_dec_ref(v___x_2811_);
return v_res_2815_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2817_, lean_object* v_x_2818_, size_t v_x_2819_, size_t v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
if (lean_obj_tag(v_x_2818_) == 0)
{
lean_object* v_es_2823_; size_t v___x_2824_; size_t v___x_2825_; lean_object* v_j_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_es_2823_ = lean_ctor_get(v_x_2818_, 0);
v___x_2824_ = ((size_t)31ULL);
v___x_2825_ = lean_usize_land(v_x_2819_, v___x_2824_);
v_j_2826_ = lean_usize_to_nat(v___x_2825_);
v___x_2827_ = lean_array_get_size(v_es_2823_);
v___x_2828_ = lean_nat_dec_lt(v_j_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_dec(v_j_2826_);
lean_dec(v_x_2822_);
lean_dec_ref(v_x_2821_);
return v_x_2818_;
}
else
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2867_; 
lean_inc_ref(v_es_2823_);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_x_2818_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v_x_2818_, 0);
lean_dec(v_unused_2868_);
v___x_2830_ = v_x_2818_;
v_isShared_2831_ = v_isSharedCheck_2867_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v_x_2818_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2867_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_v_2832_; lean_object* v___x_2833_; lean_object* v_xs_x27_2834_; lean_object* v___y_2836_; 
v_v_2832_ = lean_array_fget(v_es_2823_, v_j_2826_);
v___x_2833_ = lean_box(0);
v_xs_x27_2834_ = lean_array_fset(v_es_2823_, v_j_2826_, v___x_2833_);
switch(lean_obj_tag(v_v_2832_))
{
case 0:
{
lean_object* v_key_2841_; lean_object* v_val_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2852_; 
v_key_2841_ = lean_ctor_get(v_v_2832_, 0);
v_val_2842_ = lean_ctor_get(v_v_2832_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_v_2832_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2844_ = v_v_2832_;
v_isShared_2845_ = v_isSharedCheck_2852_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_val_2842_);
lean_inc(v_key_2841_);
lean_dec(v_v_2832_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2852_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
uint8_t v___x_2846_; 
lean_inc(v_key_2841_);
lean_inc_ref(v_x_2821_);
v___x_2846_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2817_, v_x_2821_, v_key_2841_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_del_object(v___x_2844_);
v___x_2847_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2841_, v_val_2842_, v_x_2821_, v_x_2822_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v___y_2836_ = v___x_2848_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2850_; 
lean_dec(v_val_2842_);
lean_dec(v_key_2841_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v_x_2822_);
lean_ctor_set(v___x_2844_, 0, v_x_2821_);
v___x_2850_ = v___x_2844_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_x_2821_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_x_2822_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v___y_2836_ = v___x_2850_;
goto v___jp_2835_;
}
}
}
}
case 1:
{
lean_object* v_node_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2865_; 
v_node_2853_ = lean_ctor_get(v_v_2832_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_v_2832_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2855_ = v_v_2832_;
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_node_2853_);
lean_dec(v_v_2832_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2857_ = ((size_t)5ULL);
v___x_2858_ = lean_usize_shift_right(v_x_2819_, v___x_2857_);
v___x_2859_ = ((size_t)1ULL);
v___x_2860_ = lean_usize_add(v_x_2820_, v___x_2859_);
v___x_2861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2817_, v_node_2853_, v___x_2858_, v___x_2860_, v_x_2821_, v_x_2822_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2861_);
v___x_2863_ = v___x_2855_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v___y_2836_ = v___x_2863_;
goto v___jp_2835_;
}
}
}
default: 
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_x_2821_);
lean_ctor_set(v___x_2866_, 1, v_x_2822_);
v___y_2836_ = v___x_2866_;
goto v___jp_2835_;
}
}
v___jp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = lean_array_fset(v_xs_x27_2834_, v_j_2826_, v___y_2836_);
lean_dec(v_j_2826_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2837_);
v___x_2839_ = v___x_2830_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_object* v_ks_2869_; lean_object* v_vs_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2888_; 
v_ks_2869_ = lean_ctor_get(v_x_2818_, 0);
v_vs_2870_ = lean_ctor_get(v_x_2818_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_x_2818_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2872_ = v_x_2818_;
v_isShared_2873_ = v_isSharedCheck_2888_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_vs_2870_);
lean_inc(v_ks_2869_);
lean_dec(v_x_2818_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2888_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_ks_2869_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_vs_2870_);
v___x_2875_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v_newNode_2876_; size_t v___x_2877_; uint8_t v___x_2878_; 
v_newNode_2876_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2817_, v___x_2875_, v_x_2821_, v_x_2822_);
v___x_2877_ = ((size_t)7ULL);
v___x_2878_ = lean_usize_dec_le(v___x_2877_, v_x_2820_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2879_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2876_);
v___x_2880_ = lean_unsigned_to_nat(4u);
v___x_2881_ = lean_nat_dec_lt(v___x_2879_, v___x_2880_);
lean_dec(v___x_2879_);
if (v___x_2881_ == 0)
{
lean_object* v_ks_2882_; lean_object* v_vs_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_ks_2882_ = lean_ctor_get(v_newNode_2876_, 0);
lean_inc_ref(v_ks_2882_);
v_vs_2883_ = lean_ctor_get(v_newNode_2876_, 1);
lean_inc_ref(v_vs_2883_);
lean_dec_ref(v_newNode_2876_);
v___x_2884_ = lean_unsigned_to_nat(0u);
v___x_2885_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2886_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2817_, v_x_2820_, v_ks_2882_, v_vs_2883_, v___x_2884_, v___x_2885_);
lean_dec_ref(v_vs_2883_);
lean_dec_ref(v_ks_2882_);
return v___x_2886_;
}
else
{
return v_newNode_2876_;
}
}
else
{
return v_newNode_2876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2889_, size_t v_depth_2890_, lean_object* v_keys_2891_, lean_object* v_vals_2892_, lean_object* v_i_2893_, lean_object* v_entries_2894_){
_start:
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = lean_array_get_size(v_keys_2891_);
v___x_2896_ = lean_nat_dec_lt(v_i_2893_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_dec(v_i_2893_);
return v_entries_2894_;
}
else
{
lean_object* v_k_2897_; lean_object* v_v_2898_; uint64_t v___x_2899_; size_t v_h_2900_; size_t v___x_2901_; lean_object* v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; size_t v_h_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_k_2897_ = lean_array_fget_borrowed(v_keys_2891_, v_i_2893_);
v_v_2898_ = lean_array_fget_borrowed(v_vals_2892_, v_i_2893_);
lean_inc_n(v_k_2897_, 2);
v___x_2899_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2889_, v_k_2897_);
v_h_2900_ = lean_uint64_to_usize(v___x_2899_);
v___x_2901_ = ((size_t)5ULL);
v___x_2902_ = lean_unsigned_to_nat(1u);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_sub(v_depth_2890_, v___x_2903_);
v___x_2905_ = lean_usize_mul(v___x_2901_, v___x_2904_);
v_h_2906_ = lean_usize_shift_right(v_h_2900_, v___x_2905_);
v___x_2907_ = lean_nat_add(v_i_2893_, v___x_2902_);
lean_dec(v_i_2893_);
lean_inc(v_v_2898_);
v___x_2908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2889_, v_entries_2894_, v_h_2906_, v_depth_2890_, v_k_2897_, v_v_2898_);
v_i_2893_ = v___x_2907_;
v_entries_2894_ = v___x_2908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2910_, lean_object* v_depth_2911_, lean_object* v_keys_2912_, lean_object* v_vals_2913_, lean_object* v_i_2914_, lean_object* v_entries_2915_){
_start:
{
size_t v_depth_boxed_2916_; lean_object* v_res_2917_; 
v_depth_boxed_2916_ = lean_unbox_usize(v_depth_2911_);
lean_dec(v_depth_2911_);
v_res_2917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2910_, v_depth_boxed_2916_, v_keys_2912_, v_vals_2913_, v_i_2914_, v_entries_2915_);
lean_dec_ref(v_vals_2913_);
lean_dec_ref(v_keys_2912_);
lean_dec_ref(v___x_2910_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
size_t v_x_26097__boxed_2924_; size_t v_x_26098__boxed_2925_; lean_object* v_res_2926_; 
v_x_26097__boxed_2924_ = lean_unbox_usize(v_x_2920_);
lean_dec(v_x_2920_);
v_x_26098__boxed_2925_ = lean_unbox_usize(v_x_2921_);
lean_dec(v_x_2921_);
v_res_2926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2918_, v_x_2919_, v_x_26097__boxed_2924_, v_x_26098__boxed_2925_, v_x_2922_, v_x_2923_);
lean_dec_ref(v___x_2918_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
uint64_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
lean_inc_ref(v_x_2929_);
v___x_2931_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2927_, v_x_2929_);
v___x_2932_ = lean_uint64_to_usize(v___x_2931_);
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2927_, v_x_2928_, v___x_2932_, v___x_2933_, v_x_2929_, v_x_2930_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2935_, v_x_2936_, v_x_2937_, v_x_2938_);
lean_dec_ref(v___x_2935_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2944_, lean_object* v_rootNew_2945_, uint8_t v_a_2946_, lean_object* v_a_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; lean_object* v_snd_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3125_; 
v___x_2955_ = lean_st_ref_get(v___y_2948_);
v_snd_2956_ = lean_ctor_get(v_a_2947_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_a_2947_, 0);
lean_dec(v_unused_3126_);
v___x_2958_ = v_a_2947_;
v_isShared_2959_ = v_isSharedCheck_3125_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snd_2956_);
lean_dec(v_a_2947_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3125_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; 
lean_inc(v_snd_2956_);
v___x_2960_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2955_, v_snd_2956_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___x_2955_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3116_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_3116_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3116_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_self_2965_; lean_object* v_next_2966_; lean_object* v_congr_2967_; lean_object* v_target_x3f_2968_; lean_object* v_proof_x3f_2969_; uint8_t v_flipped_2970_; lean_object* v_size_2971_; uint8_t v_interpreted_2972_; uint8_t v_ctor_2973_; uint8_t v_hasLambdas_2974_; uint8_t v_heqProofs_2975_; lean_object* v_idx_2976_; lean_object* v_generation_2977_; lean_object* v_mt_2978_; lean_object* v_sTerms_2979_; uint8_t v_funCC_2980_; lean_object* v_ematchDiagSource_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3114_; 
v_self_2965_ = lean_ctor_get(v_a_2961_, 0);
v_next_2966_ = lean_ctor_get(v_a_2961_, 1);
v_congr_2967_ = lean_ctor_get(v_a_2961_, 3);
v_target_x3f_2968_ = lean_ctor_get(v_a_2961_, 4);
v_proof_x3f_2969_ = lean_ctor_get(v_a_2961_, 5);
v_flipped_2970_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12);
v_size_2971_ = lean_ctor_get(v_a_2961_, 6);
v_interpreted_2972_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12 + 1);
v_ctor_2973_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12 + 2);
v_hasLambdas_2974_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12 + 3);
v_heqProofs_2975_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12 + 4);
v_idx_2976_ = lean_ctor_get(v_a_2961_, 7);
v_generation_2977_ = lean_ctor_get(v_a_2961_, 8);
v_mt_2978_ = lean_ctor_get(v_a_2961_, 9);
v_sTerms_2979_ = lean_ctor_get(v_a_2961_, 10);
v_funCC_2980_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2981_ = lean_ctor_get(v_a_2961_, 11);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_a_2961_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; 
v_unused_3115_ = lean_ctor_get(v_a_2961_, 2);
lean_dec(v_unused_3115_);
v___x_2983_ = v_a_2961_;
v_isShared_2984_ = v_isSharedCheck_3114_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_ematchDiagSource_2981_);
lean_inc(v_sTerms_2979_);
lean_inc(v_mt_2978_);
lean_inc(v_generation_2977_);
lean_inc(v_idx_2976_);
lean_inc(v_size_2971_);
lean_inc(v_proof_x3f_2969_);
lean_inc(v_target_x3f_2968_);
lean_inc(v_congr_2967_);
lean_inc(v_next_2966_);
lean_inc(v_self_2965_);
lean_dec(v_a_2961_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3114_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___y_3002_; lean_object* v___x_3012_; 
v___x_2985_ = lean_box(0);
lean_inc(v_ematchDiagSource_2981_);
lean_inc(v_sTerms_2979_);
lean_inc(v_mt_2978_);
lean_inc(v_generation_2977_);
lean_inc(v_idx_2976_);
lean_inc(v_size_2971_);
lean_inc(v_proof_x3f_2969_);
lean_inc(v_target_x3f_2968_);
lean_inc_ref(v_rootNew_2945_);
lean_inc_ref(v_next_2966_);
lean_inc_ref(v_self_2965_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 2, v_rootNew_2945_);
v___x_3012_ = v___x_2983_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_self_2965_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_next_2966_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_rootNew_2945_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_congr_2967_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_target_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_3113_, 5, v_proof_x3f_2969_);
lean_ctor_set(v_reuseFailAlloc_3113_, 6, v_size_2971_);
lean_ctor_set(v_reuseFailAlloc_3113_, 7, v_idx_2976_);
lean_ctor_set(v_reuseFailAlloc_3113_, 8, v_generation_2977_);
lean_ctor_set(v_reuseFailAlloc_3113_, 9, v_mt_2978_);
lean_ctor_set(v_reuseFailAlloc_3113_, 10, v_sTerms_2979_);
lean_ctor_set(v_reuseFailAlloc_3113_, 11, v_ematchDiagSource_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12, v_flipped_2970_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12 + 1, v_interpreted_2972_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12 + 2, v_ctor_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12 + 3, v_hasLambdas_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12 + 4, v_heqProofs_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, sizeof(void*)*12 + 5, v_funCC_2980_);
v___x_3012_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3011_;
}
v___jp_2986_:
{
size_t v___x_2987_; size_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = lean_ptr_addr(v_next_2966_);
v___x_2988_ = lean_ptr_addr(v_lhs_2944_);
v___x_2989_ = lean_usize_dec_eq(v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2991_; 
lean_del_object(v___x_2963_);
lean_dec(v_snd_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_next_2966_);
lean_ctor_set(v___x_2958_, 0, v___x_2985_);
v___x_2991_ = v___x_2958_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_next_2966_);
v___x_2991_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
v_a_2947_ = v___x_2991_;
goto _start;
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
lean_dec_ref(v_next_2966_);
lean_dec_ref(v_rootNew_2945_);
v___x_2994_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2994_);
v___x_2996_ = v___x_2958_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_snd_2956_);
v___x_2996_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2996_);
v___x_2998_ = v___x_2963_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
v___jp_3001_:
{
if (lean_obj_tag(v___y_3002_) == 0)
{
lean_dec_ref_known(v___y_3002_, 1);
goto v___jp_2986_;
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_next_2966_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
lean_dec(v_snd_2956_);
lean_dec_ref(v_rootNew_2945_);
v_a_3003_ = lean_ctor_get(v___y_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___y_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___y_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___y_3002_);
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
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
lean_inc_ref(v___x_3012_);
lean_inc_ref(v_self_2965_);
v___x_3013_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2965_, v___x_3012_, v___y_2948_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_dec_ref_known(v___x_3013_, 1);
if (v_a_2946_ == 0)
{
lean_dec_ref(v___x_3012_);
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
goto v___jp_2986_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3015_ = lean_unsigned_to_nat(3u);
v___x_3016_ = l_Lean_Expr_isAppOfArity(v_self_2965_, v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_dec_ref(v___x_3012_);
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
goto v___jp_2986_;
}
else
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3012_);
lean_dec_ref(v___x_3012_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v_toGoalState_3019_; lean_object* v_enodeMap_3020_; lean_object* v_congrTable_3021_; lean_object* v___x_3022_; 
v___x_3018_ = lean_st_ref_get(v___y_2948_);
v_toGoalState_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc_ref(v_toGoalState_3019_);
lean_dec(v___x_3018_);
v_enodeMap_3020_ = lean_ctor_get(v_toGoalState_3019_, 1);
lean_inc_ref(v_enodeMap_3020_);
v_congrTable_3021_ = lean_ctor_get(v_toGoalState_3019_, 4);
lean_inc_ref(v_congrTable_3021_);
lean_dec_ref(v_toGoalState_3019_);
lean_inc_ref(v_self_2965_);
v___x_3022_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3020_, v_congrTable_3021_, v_self_2965_);
lean_dec_ref(v_congrTable_3021_);
lean_dec_ref(v_enodeMap_3020_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
goto v___jp_2986_;
}
else
{
lean_object* v_val_3023_; lean_object* v_fst_3024_; lean_object* v___x_3025_; 
v_val_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_fst_3024_ = lean_ctor_get(v_val_3023_, 0);
lean_inc(v_fst_3024_);
lean_dec(v_val_3023_);
v___x_3025_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3024_, v___y_2949_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; uint8_t v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = lean_unbox(v_a_3026_);
lean_dec(v_a_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; lean_object* v_toGoalState_3029_; lean_object* v_mvarId_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3104_; 
v___x_3028_ = lean_st_ref_take(v___y_2948_);
v_toGoalState_3029_ = lean_ctor_get(v___x_3028_, 0);
v_mvarId_3030_ = lean_ctor_get(v___x_3028_, 1);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3032_ = v___x_3028_;
v_isShared_3033_ = v_isSharedCheck_3104_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_mvarId_3030_);
lean_inc(v_toGoalState_3029_);
lean_dec(v___x_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3104_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v_nextDeclIdx_3034_; lean_object* v_enodeMap_3035_; lean_object* v_exprs_3036_; lean_object* v_parents_3037_; lean_object* v_congrTable_3038_; lean_object* v_appMap_3039_; lean_object* v_indicesFound_3040_; lean_object* v_newFacts_3041_; uint8_t v_inconsistent_3042_; lean_object* v_nextIdx_3043_; lean_object* v_newRawFacts_3044_; lean_object* v_facts_3045_; lean_object* v_extThms_3046_; lean_object* v_ematch_3047_; lean_object* v_inj_3048_; lean_object* v_split_3049_; lean_object* v_clean_3050_; lean_object* v_sstates_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3103_; 
v_nextDeclIdx_3034_ = lean_ctor_get(v_toGoalState_3029_, 0);
v_enodeMap_3035_ = lean_ctor_get(v_toGoalState_3029_, 1);
v_exprs_3036_ = lean_ctor_get(v_toGoalState_3029_, 2);
v_parents_3037_ = lean_ctor_get(v_toGoalState_3029_, 3);
v_congrTable_3038_ = lean_ctor_get(v_toGoalState_3029_, 4);
v_appMap_3039_ = lean_ctor_get(v_toGoalState_3029_, 5);
v_indicesFound_3040_ = lean_ctor_get(v_toGoalState_3029_, 6);
v_newFacts_3041_ = lean_ctor_get(v_toGoalState_3029_, 7);
v_inconsistent_3042_ = lean_ctor_get_uint8(v_toGoalState_3029_, sizeof(void*)*17);
v_nextIdx_3043_ = lean_ctor_get(v_toGoalState_3029_, 8);
v_newRawFacts_3044_ = lean_ctor_get(v_toGoalState_3029_, 9);
v_facts_3045_ = lean_ctor_get(v_toGoalState_3029_, 10);
v_extThms_3046_ = lean_ctor_get(v_toGoalState_3029_, 11);
v_ematch_3047_ = lean_ctor_get(v_toGoalState_3029_, 12);
v_inj_3048_ = lean_ctor_get(v_toGoalState_3029_, 13);
v_split_3049_ = lean_ctor_get(v_toGoalState_3029_, 14);
v_clean_3050_ = lean_ctor_get(v_toGoalState_3029_, 15);
v_sstates_3051_ = lean_ctor_get(v_toGoalState_3029_, 16);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_toGoalState_3029_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3053_ = v_toGoalState_3029_;
v_isShared_3054_ = v_isSharedCheck_3103_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_sstates_3051_);
lean_inc(v_clean_3050_);
lean_inc(v_split_3049_);
lean_inc(v_inj_3048_);
lean_inc(v_ematch_3047_);
lean_inc(v_extThms_3046_);
lean_inc(v_facts_3045_);
lean_inc(v_newRawFacts_3044_);
lean_inc(v_nextIdx_3043_);
lean_inc(v_newFacts_3041_);
lean_inc(v_indicesFound_3040_);
lean_inc(v_appMap_3039_);
lean_inc(v_congrTable_3038_);
lean_inc(v_parents_3037_);
lean_inc(v_exprs_3036_);
lean_inc(v_enodeMap_3035_);
lean_inc(v_nextDeclIdx_3034_);
lean_dec(v_toGoalState_3029_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3103_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3055_ = lean_box(0);
lean_inc_ref(v_self_2965_);
v___x_3056_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3035_, v_congrTable_3038_, v_self_2965_, v___x_3055_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 4, v___x_3056_);
v___x_3058_ = v___x_3053_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_nextDeclIdx_3034_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_enodeMap_3035_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_exprs_3036_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_parents_3037_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3102_, 5, v_appMap_3039_);
lean_ctor_set(v_reuseFailAlloc_3102_, 6, v_indicesFound_3040_);
lean_ctor_set(v_reuseFailAlloc_3102_, 7, v_newFacts_3041_);
lean_ctor_set(v_reuseFailAlloc_3102_, 8, v_nextIdx_3043_);
lean_ctor_set(v_reuseFailAlloc_3102_, 9, v_newRawFacts_3044_);
lean_ctor_set(v_reuseFailAlloc_3102_, 10, v_facts_3045_);
lean_ctor_set(v_reuseFailAlloc_3102_, 11, v_extThms_3046_);
lean_ctor_set(v_reuseFailAlloc_3102_, 12, v_ematch_3047_);
lean_ctor_set(v_reuseFailAlloc_3102_, 13, v_inj_3048_);
lean_ctor_set(v_reuseFailAlloc_3102_, 14, v_split_3049_);
lean_ctor_set(v_reuseFailAlloc_3102_, 15, v_clean_3050_);
lean_ctor_set(v_reuseFailAlloc_3102_, 16, v_sstates_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3102_, sizeof(void*)*17, v_inconsistent_3042_);
v___x_3058_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3058_);
v___x_3060_ = v___x_3032_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_mvarId_3030_);
v___x_3060_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_st_ref_put(v___y_2948_, v___x_3060_);
lean_inc_ref(v_rootNew_2945_);
lean_inc_ref(v_next_2966_);
lean_inc_ref_n(v_self_2965_, 3);
v___x_3062_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3062_, 0, v_self_2965_);
lean_ctor_set(v___x_3062_, 1, v_next_2966_);
lean_ctor_set(v___x_3062_, 2, v_rootNew_2945_);
lean_ctor_set(v___x_3062_, 3, v_self_2965_);
lean_ctor_set(v___x_3062_, 4, v_target_x3f_2968_);
lean_ctor_set(v___x_3062_, 5, v_proof_x3f_2969_);
lean_ctor_set(v___x_3062_, 6, v_size_2971_);
lean_ctor_set(v___x_3062_, 7, v_idx_2976_);
lean_ctor_set(v___x_3062_, 8, v_generation_2977_);
lean_ctor_set(v___x_3062_, 9, v_mt_2978_);
lean_ctor_set(v___x_3062_, 10, v_sTerms_2979_);
lean_ctor_set(v___x_3062_, 11, v_ematchDiagSource_2981_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12, v_flipped_2970_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12 + 1, v_interpreted_2972_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12 + 2, v_ctor_2973_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12 + 3, v_hasLambdas_2974_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12 + 4, v_heqProofs_2975_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*12 + 5, v_funCC_2980_);
v___x_3063_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2965_, v___x_3062_, v___y_2948_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref_known(v___x_3063_, 1);
v___x_3064_ = lean_st_ref_get(v___y_2948_);
lean_inc(v_fst_3024_);
v___x_3065_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3064_, v_fst_3024_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___x_3064_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v_self_3067_; lean_object* v_next_3068_; lean_object* v_root_3069_; lean_object* v_target_x3f_3070_; lean_object* v_proof_x3f_3071_; uint8_t v_flipped_3072_; lean_object* v_size_3073_; uint8_t v_interpreted_3074_; uint8_t v_ctor_3075_; uint8_t v_hasLambdas_3076_; uint8_t v_heqProofs_3077_; lean_object* v_idx_3078_; lean_object* v_generation_3079_; lean_object* v_mt_3080_; lean_object* v_sTerms_3081_; uint8_t v_funCC_3082_; lean_object* v_ematchDiagSource_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v_self_3067_ = lean_ctor_get(v_a_3066_, 0);
v_next_3068_ = lean_ctor_get(v_a_3066_, 1);
v_root_3069_ = lean_ctor_get(v_a_3066_, 2);
v_target_x3f_3070_ = lean_ctor_get(v_a_3066_, 4);
v_proof_x3f_3071_ = lean_ctor_get(v_a_3066_, 5);
v_flipped_3072_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12);
v_size_3073_ = lean_ctor_get(v_a_3066_, 6);
v_interpreted_3074_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12 + 1);
v_ctor_3075_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12 + 2);
v_hasLambdas_3076_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12 + 3);
v_heqProofs_3077_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12 + 4);
v_idx_3078_ = lean_ctor_get(v_a_3066_, 7);
v_generation_3079_ = lean_ctor_get(v_a_3066_, 8);
v_mt_3080_ = lean_ctor_get(v_a_3066_, 9);
v_sTerms_3081_ = lean_ctor_get(v_a_3066_, 10);
v_funCC_3082_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3083_ = lean_ctor_get(v_a_3066_, 11);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_a_3066_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_a_3066_, 3);
lean_dec(v_unused_3092_);
v___x_3085_ = v_a_3066_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_ematchDiagSource_3083_);
lean_inc(v_sTerms_3081_);
lean_inc(v_mt_3080_);
lean_inc(v_generation_3079_);
lean_inc(v_idx_3078_);
lean_inc(v_size_3073_);
lean_inc(v_proof_x3f_3071_);
lean_inc(v_target_x3f_3070_);
lean_inc(v_root_3069_);
lean_inc(v_next_3068_);
lean_inc(v_self_3067_);
lean_dec(v_a_3066_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 3, v_self_2965_);
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_self_3067_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_next_3068_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_root_3069_);
lean_ctor_set(v_reuseFailAlloc_3090_, 3, v_self_2965_);
lean_ctor_set(v_reuseFailAlloc_3090_, 4, v_target_x3f_3070_);
lean_ctor_set(v_reuseFailAlloc_3090_, 5, v_proof_x3f_3071_);
lean_ctor_set(v_reuseFailAlloc_3090_, 6, v_size_3073_);
lean_ctor_set(v_reuseFailAlloc_3090_, 7, v_idx_3078_);
lean_ctor_set(v_reuseFailAlloc_3090_, 8, v_generation_3079_);
lean_ctor_set(v_reuseFailAlloc_3090_, 9, v_mt_3080_);
lean_ctor_set(v_reuseFailAlloc_3090_, 10, v_sTerms_3081_);
lean_ctor_set(v_reuseFailAlloc_3090_, 11, v_ematchDiagSource_3083_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12, v_flipped_3072_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12 + 1, v_interpreted_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12 + 2, v_ctor_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12 + 3, v_hasLambdas_3076_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12 + 4, v_heqProofs_3077_);
lean_ctor_set_uint8(v_reuseFailAlloc_3090_, sizeof(void*)*12 + 5, v_funCC_3082_);
v___x_3088_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3024_, v___x_3088_, v___y_2948_);
v___y_3002_ = v___x_3089_;
goto v___jp_3001_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_fst_3024_);
lean_dec_ref(v_next_2966_);
lean_dec_ref(v_self_2965_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
lean_dec(v_snd_2956_);
lean_dec_ref(v_rootNew_2945_);
v_a_3093_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3065_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3065_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_dec(v_fst_3024_);
lean_dec_ref(v_self_2965_);
v___y_3002_ = v___x_3063_;
goto v___jp_3001_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3024_);
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
goto v___jp_2986_;
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_fst_3024_);
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_next_2966_);
lean_dec_ref(v_self_2965_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2958_);
lean_dec(v_snd_2956_);
lean_dec_ref(v_rootNew_2945_);
v_a_3105_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3025_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3025_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
goto v___jp_2986_;
}
}
}
}
else
{
lean_dec_ref(v___x_3012_);
lean_dec(v_ematchDiagSource_2981_);
lean_dec(v_sTerms_2979_);
lean_dec(v_mt_2978_);
lean_dec(v_generation_2977_);
lean_dec(v_idx_2976_);
lean_dec(v_size_2971_);
lean_dec(v_proof_x3f_2969_);
lean_dec(v_target_x3f_2968_);
lean_dec_ref(v_self_2965_);
v___y_3002_ = v___x_3013_;
goto v___jp_3001_;
}
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_del_object(v___x_2958_);
lean_dec(v_snd_2956_);
lean_dec_ref(v_rootNew_2945_);
v_a_3117_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_2960_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_2960_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3127_, lean_object* v_rootNew_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
uint8_t v_a_26281__boxed_3138_; lean_object* v_res_3139_; 
v_a_26281__boxed_3138_ = lean_unbox(v_a_3129_);
v_res_3139_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3127_, v_rootNew_3128_, v_a_26281__boxed_3138_, v_a_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v_lhs_3127_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3140_, lean_object* v_rootNew_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3141_, v_a_3146_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = lean_box(0);
lean_inc_ref(v_lhs_3140_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v_lhs_3140_);
v___x_3157_ = lean_unbox(v_a_3154_);
lean_dec(v_a_3154_);
v___x_3158_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3140_, v_rootNew_3141_, v___x_3157_, v___x_3156_, v_a_3142_, v_a_3146_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec_ref(v_lhs_3140_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3172_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v_fst_3163_; 
v_fst_3163_ = lean_ctor_get(v_a_3159_, 0);
lean_inc(v_fst_3163_);
lean_dec(v_a_3159_);
if (lean_obj_tag(v_fst_3163_) == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_box(0);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3164_);
v___x_3166_ = v___x_3161_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
else
{
lean_object* v_val_3168_; lean_object* v___x_3170_; 
v_val_3168_ = lean_ctor_get(v_fst_3163_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v_fst_3163_, 1);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v_val_3168_);
v___x_3170_ = v___x_3161_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_val_3168_);
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
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3158_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3158_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v_rootNew_3141_);
lean_dec_ref(v_lhs_3140_);
v_a_3181_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3153_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3153_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3189_, lean_object* v_rootNew_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3189_, v_rootNew_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec(v_a_3191_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3203_, lean_object* v_00_u03b2_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3203_, v_x_3205_, v_x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3208_, lean_object* v_00_u03b2_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3208_, v_00_u03b2_3209_, v_x_3210_, v_x_3211_);
lean_dec_ref(v_x_3210_);
lean_dec_ref(v___x_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3213_, v_x_3215_, v_x_3216_, v_x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3219_, lean_object* v_00_u03b2_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3219_, v_00_u03b2_3220_, v_x_3221_, v_x_3222_, v_x_3223_);
lean_dec_ref(v___x_3219_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3225_, lean_object* v_rootNew_3226_, uint8_t v_a_3227_, lean_object* v_inst_3228_, lean_object* v_a_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3225_, v_rootNew_3226_, v_a_3227_, v_a_3229_, v___y_3230_, v___y_3234_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3242_, lean_object* v_rootNew_3243_, lean_object* v_a_3244_, lean_object* v_inst_3245_, lean_object* v_a_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
uint8_t v_a_26640__boxed_3258_; lean_object* v_res_3259_; 
v_a_26640__boxed_3258_ = lean_unbox(v_a_3244_);
v_res_3259_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3242_, v_rootNew_3243_, v_a_26640__boxed_3258_, v_inst_3245_, v_a_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v_lhs_3242_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3260_, lean_object* v_00_u03b2_3261_, lean_object* v_x_3262_, size_t v_x_3263_, lean_object* v_x_3264_){
_start:
{
lean_object* v___x_3265_; 
lean_inc_ref(v_x_3262_);
v___x_3265_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3260_, v_x_3262_, v_x_3263_, v_x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
size_t v_x_26683__boxed_3271_; lean_object* v_res_3272_; 
v_x_26683__boxed_3271_ = lean_unbox_usize(v_x_3269_);
lean_dec(v_x_3269_);
v_res_3272_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3266_, v_00_u03b2_3267_, v_x_3268_, v_x_26683__boxed_3271_, v_x_3270_);
lean_dec_ref(v_x_3268_);
lean_dec_ref(v___x_3266_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3273_, lean_object* v_00_u03b2_3274_, lean_object* v_x_3275_, size_t v_x_3276_, size_t v_x_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3273_, v_x_3275_, v_x_3276_, v_x_3277_, v_x_3278_, v_x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3281_, lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
size_t v_x_26697__boxed_3288_; size_t v_x_26698__boxed_3289_; lean_object* v_res_3290_; 
v_x_26697__boxed_3288_ = lean_unbox_usize(v_x_3284_);
lean_dec(v_x_3284_);
v_x_26698__boxed_3289_ = lean_unbox_usize(v_x_3285_);
lean_dec(v_x_3285_);
v_res_3290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3281_, v_00_u03b2_3282_, v_x_3283_, v_x_26697__boxed_3288_, v_x_26698__boxed_3289_, v_x_3286_, v_x_3287_);
lean_dec_ref(v___x_3281_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3291_, lean_object* v_00_u03b2_3292_, lean_object* v_keys_3293_, lean_object* v_vals_3294_, lean_object* v_heq_3295_, lean_object* v_i_3296_, lean_object* v_k_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3291_, v_keys_3293_, v_vals_3294_, v_i_3296_, v_k_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3299_, lean_object* v_00_u03b2_3300_, lean_object* v_keys_3301_, lean_object* v_vals_3302_, lean_object* v_heq_3303_, lean_object* v_i_3304_, lean_object* v_k_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3299_, v_00_u03b2_3300_, v_keys_3301_, v_vals_3302_, v_heq_3303_, v_i_3304_, v_k_3305_);
lean_dec_ref(v_vals_3302_);
lean_dec_ref(v_keys_3301_);
lean_dec_ref(v___x_3299_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3307_, lean_object* v_00_u03b2_3308_, lean_object* v_n_3309_, lean_object* v_k_3310_, lean_object* v_v_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3307_, v_n_3309_, v_k_3310_, v_v_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_n_3315_, lean_object* v_k_3316_, lean_object* v_v_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3313_, v_00_u03b2_3314_, v_n_3315_, v_k_3316_, v_v_3317_);
lean_dec_ref(v___x_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3319_, lean_object* v_00_u03b2_3320_, size_t v_depth_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_entries_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3319_, v_depth_3321_, v_keys_3322_, v_vals_3323_, v_i_3325_, v_entries_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3328_, lean_object* v_00_u03b2_3329_, lean_object* v_depth_3330_, lean_object* v_keys_3331_, lean_object* v_vals_3332_, lean_object* v_heq_3333_, lean_object* v_i_3334_, lean_object* v_entries_3335_){
_start:
{
size_t v_depth_boxed_3336_; lean_object* v_res_3337_; 
v_depth_boxed_3336_ = lean_unbox_usize(v_depth_3330_);
lean_dec(v_depth_3330_);
v_res_3337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3328_, v_00_u03b2_3329_, v_depth_boxed_3336_, v_keys_3331_, v_vals_3332_, v_heq_3333_, v_i_3334_, v_entries_3335_);
lean_dec_ref(v_vals_3332_);
lean_dec_ref(v_keys_3331_);
lean_dec_ref(v___x_3328_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3338_, lean_object* v_00_u03b2_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3338_, v_x_3340_, v_x_3341_, v_x_3342_, v_x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3345_, lean_object* v_00_u03b2_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3345_, v_00_u03b2_3346_, v_x_3347_, v_x_3348_, v_x_3349_, v_x_3350_);
lean_dec_ref(v___x_3345_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3352_, lean_object* v_b_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
if (lean_obj_tag(v_as_x27_3352_) == 0)
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_b_3353_);
return v___x_3365_;
}
else
{
lean_object* v_head_3366_; lean_object* v_tail_3367_; lean_object* v___x_3368_; 
v_head_3366_ = lean_ctor_get(v_as_x27_3352_, 0);
v_tail_3367_ = lean_ctor_get(v_as_x27_3352_, 1);
lean_inc(v_head_3366_);
v___x_3368_ = l_Lean_Meta_Grind_propagateUp(v_head_3366_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3369_; 
lean_dec_ref_known(v___x_3368_, 1);
v___x_3369_ = lean_box(0);
v_as_x27_3352_ = v_tail_3367_;
v_b_3353_ = v___x_3369_;
goto _start;
}
else
{
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3371_, v_b_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v_as_x27_3371_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3385_, lean_object* v_b_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
if (lean_obj_tag(v_as_x27_3385_) == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_b_3386_);
return v___x_3398_;
}
else
{
lean_object* v_head_3399_; lean_object* v_tail_3400_; lean_object* v___x_3401_; 
v_head_3399_ = lean_ctor_get(v_as_x27_3385_, 0);
v_tail_3400_ = lean_ctor_get(v_as_x27_3385_, 1);
lean_inc(v_head_3399_);
v___x_3401_ = l_Lean_Meta_Grind_propagateDown(v_head_3399_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; 
lean_dec_ref_known(v___x_3401_, 1);
v___x_3402_ = lean_box(0);
v_as_x27_3385_ = v_tail_3400_;
v_b_3386_ = v___x_3402_;
goto _start;
}
else
{
return v___x_3401_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3404_, v_b_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec(v_as_x27_3404_);
return v_res_3417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_cls_3421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3422_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3423_ = l_Lean_Name_append(v___x_3422_, v_cls_3421_);
return v___x_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3432_ = l_Lean_stringToMessageData(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3436_, uint8_t v_isHEq_3437_, lean_object* v_lhs_3438_, lean_object* v_rhs_3439_, lean_object* v_lhsNode_3440_, lean_object* v_rhsNode_3441_, lean_object* v_lhsRoot_3442_, lean_object* v_rhsRoot_3443_, uint8_t v_flipped_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3509_; uint8_t v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; uint8_t v___y_3544_; uint8_t v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; uint8_t v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3615_; uint8_t v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_toCold_3694_; lean_object* v_options_3695_; lean_object* v_inheritedTraceOptions_3696_; uint8_t v_hasTrace_3697_; lean_object* v_cls_3698_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_fns_u2082_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_fns_u2081_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; 
v_toCold_3694_ = lean_ctor_get(v_a_3453_, 0);
v_options_3695_ = lean_ctor_get(v_toCold_3694_, 2);
v_inheritedTraceOptions_3696_ = lean_ctor_get(v_toCold_3694_, 11);
v_hasTrace_3697_ = lean_ctor_get_uint8(v_options_3695_, sizeof(void*)*1);
v_cls_3698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3697_ == 0)
{
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
goto v___jp_3817_;
}
else
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3696_, v_options_3695_, v___x_3898_);
if (v___x_3899_ == 0)
{
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
goto v___jp_3817_;
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Meta_Grind_updateLastTag(v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref_known(v___x_3900_, 1);
lean_inc_ref(v_lhs_3438_);
v___x_3901_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3438_, v_a_3445_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
lean_inc_ref(v_rhs_3439_);
v___x_3903_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3439_, v_a_3445_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v_a_3902_);
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
lean_ctor_set(v___x_3909_, 1, v_a_3904_);
v___x_3910_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3698_, v___x_3909_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_dec_ref_known(v___x_3910_, 1);
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
goto v___jp_3817_;
}
else
{
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhsNode_3440_);
lean_dec_ref(v_rhs_3439_);
lean_dec_ref(v_lhs_3438_);
lean_dec_ref(v_proof_3436_);
return v___x_3910_;
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v_a_3902_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhsNode_3440_);
lean_dec_ref(v_rhs_3439_);
lean_dec_ref(v_lhs_3438_);
lean_dec_ref(v_proof_3436_);
v_a_3911_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3903_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3903_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhsNode_3440_);
lean_dec_ref(v_rhs_3439_);
lean_dec_ref(v_lhs_3438_);
lean_dec_ref(v_proof_3436_);
v_a_3919_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3901_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3901_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhsNode_3440_);
lean_dec_ref(v_rhs_3439_);
lean_dec_ref(v_lhs_3438_);
lean_dec_ref(v_proof_3436_);
return v___x_3900_;
}
}
}
v___jp_3456_:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3463_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3499_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3499_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3499_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_unbox(v_a_3474_);
lean_dec(v_a_3474_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_del_object(v___x_3476_);
v___x_3479_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3462_);
lean_dec(v___y_3462_);
v___x_3480_ = lean_box(0);
v___x_3481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3479_, v___x_3480_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___x_3479_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3482_; 
lean_dec_ref_known(v___x_3481_, 1);
v___x_3482_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3459_, v___x_3480_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3482_, 1);
v___x_3483_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3458_, v___y_3461_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3458_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref_known(v___x_3483_, 1);
v___x_3484_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3460_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3493_; 
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v___x_3484_, 0);
lean_dec(v_unused_3494_);
v___x_3486_ = v___x_3484_;
v_isShared_3487_ = v_isSharedCheck_3493_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v___x_3484_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3493_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
uint8_t v___x_3488_; 
v___x_3488_ = l_Lean_Expr_isTrue(v___y_3457_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3490_; 
lean_dec(v___y_3459_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3480_);
v___x_3490_ = v___x_3486_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3480_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
else
{
lean_object* v___x_3492_; 
lean_del_object(v___x_3486_);
v___x_3492_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3459_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3459_);
return v___x_3492_;
}
}
}
else
{
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3457_);
return v___x_3484_;
}
}
else
{
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3457_);
return v___x_3483_;
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v___x_3482_;
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v___x_3481_;
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3457_);
v___x_3495_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3495_);
v___x_3497_ = v___x_3476_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3457_);
v_a_3500_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3473_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3473_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
v___jp_3508_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_inc_ref(v___y_3534_);
v___x_3545_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3545_, 0, v___y_3534_);
lean_ctor_set(v___x_3545_, 1, v___y_3531_);
lean_ctor_set(v___x_3545_, 2, v___y_3541_);
lean_ctor_set(v___x_3545_, 3, v___y_3526_);
lean_ctor_set(v___x_3545_, 4, v___y_3520_);
lean_ctor_set(v___x_3545_, 5, v___y_3538_);
lean_ctor_set(v___x_3545_, 6, v___y_3529_);
lean_ctor_set(v___x_3545_, 7, v___y_3528_);
lean_ctor_set(v___x_3545_, 8, v___y_3535_);
lean_ctor_set(v___x_3545_, 9, v___y_3518_);
lean_ctor_set(v___x_3545_, 10, v___y_3515_);
lean_ctor_set(v___x_3545_, 11, v___y_3537_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12, v___y_3510_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12 + 1, v___y_3511_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12 + 2, v___y_3536_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12 + 3, v___y_3533_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12 + 4, v___y_3544_);
lean_ctor_set_uint8(v___x_3545_, sizeof(void*)*12 + 5, v___y_3516_);
lean_inc_ref(v___y_3519_);
v___x_3546_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3519_, v___x_3545_, v___y_3514_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3546_, 1);
lean_inc_ref(v___y_3530_);
v___x_3547_ = l_Lean_Meta_Grind_propagateBeta(v___y_3530_, v___y_3540_, v___y_3514_, v___y_3532_, v___y_3524_, v___y_3517_, v___y_3542_, v___y_3523_, v___y_3513_, v___y_3522_, v___y_3539_, v___y_3527_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; 
lean_dec_ref_known(v___x_3547_, 1);
lean_inc_ref(v___y_3543_);
v___x_3548_ = l_Lean_Meta_Grind_propagateBeta(v___y_3543_, v___y_3512_, v___y_3514_, v___y_3532_, v___y_3524_, v___y_3517_, v___y_3542_, v___y_3523_, v___y_3513_, v___y_3522_, v___y_3539_, v___y_3527_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; 
lean_dec_ref_known(v___x_3548_, 1);
v___x_3549_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3443_, v_lhsRoot_3442_, v___y_3514_, v___y_3513_, v___y_3522_, v___y_3539_, v___y_3527_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3509_, v___y_3514_);
lean_dec_ref(v___y_3509_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
lean_inc_ref(v___y_3519_);
v___x_3552_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3525_, v___y_3519_, v___y_3514_, v___y_3532_, v___y_3524_, v___y_3517_, v___y_3542_, v___y_3523_, v___y_3513_, v___y_3522_, v___y_3539_, v___y_3527_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v___x_3553_; 
lean_dec_ref_known(v___x_3552_, 1);
v___x_3553_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3514_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; uint8_t v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = lean_unbox(v_a_3554_);
lean_dec(v_a_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3534_, v___y_3514_, v___y_3532_, v___y_3524_, v___y_3517_, v___y_3542_, v___y_3523_, v___y_3513_, v___y_3522_, v___y_3539_, v___y_3527_);
lean_dec_ref(v___y_3534_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref_known(v___x_3556_, 1);
v___y_3457_ = v___y_3519_;
v___y_3458_ = v___y_3530_;
v___y_3459_ = v___y_3521_;
v___y_3460_ = v_a_3550_;
v___y_3461_ = v___y_3543_;
v___y_3462_ = v___y_3525_;
v___y_3463_ = v___y_3514_;
v___y_3464_ = v___y_3532_;
v___y_3465_ = v___y_3524_;
v___y_3466_ = v___y_3517_;
v___y_3467_ = v___y_3542_;
v___y_3468_ = v___y_3523_;
v___y_3469_ = v___y_3513_;
v___y_3470_ = v___y_3522_;
v___y_3471_ = v___y_3539_;
v___y_3472_ = v___y_3527_;
goto v___jp_3456_;
}
else
{
lean_dec(v_a_3550_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
return v___x_3556_;
}
}
else
{
lean_dec_ref(v___y_3534_);
v___y_3457_ = v___y_3519_;
v___y_3458_ = v___y_3530_;
v___y_3459_ = v___y_3521_;
v___y_3460_ = v_a_3550_;
v___y_3461_ = v___y_3543_;
v___y_3462_ = v___y_3525_;
v___y_3463_ = v___y_3514_;
v___y_3464_ = v___y_3532_;
v___y_3465_ = v___y_3524_;
v___y_3466_ = v___y_3517_;
v___y_3467_ = v___y_3542_;
v___y_3468_ = v___y_3523_;
v___y_3469_ = v___y_3513_;
v___y_3470_ = v___y_3522_;
v___y_3471_ = v___y_3539_;
v___y_3472_ = v___y_3527_;
goto v___jp_3456_;
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec(v_a_3550_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
v_a_3557_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3553_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3553_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_dec(v_a_3550_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
return v___x_3552_;
}
}
else
{
lean_dec(v_a_3550_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
return v___x_3551_;
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
v_a_3565_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3549_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3549_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
return v___x_3548_;
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
return v___x_3547_;
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3525_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
return v___x_3546_;
}
}
v___jp_3573_:
{
if (v_isHEq_3437_ == 0)
{
if (v___y_3592_ == 0)
{
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3574_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3581_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3610_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3604_;
v___y_3539_ = v___y_3606_;
v___y_3540_ = v___y_3605_;
v___y_3541_ = v___y_3607_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v___y_3585_;
goto v___jp_3508_;
}
else
{
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3574_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3581_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3610_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3604_;
v___y_3539_ = v___y_3606_;
v___y_3540_ = v___y_3605_;
v___y_3541_ = v___y_3607_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v___y_3592_;
goto v___jp_3508_;
}
}
else
{
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3574_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3581_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3610_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3604_;
v___y_3539_ = v___y_3606_;
v___y_3540_ = v___y_3605_;
v___y_3541_ = v___y_3607_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v_isHEq_3437_;
goto v___jp_3508_;
}
}
v___jp_3611_:
{
lean_object* v___x_3634_; 
v___x_3634_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec_ref_known(v___x_3634_, 1);
v___x_3635_ = lean_st_ref_get(v___y_3624_);
v___x_3636_ = lean_st_ref_get(v___y_3624_);
lean_inc_ref(v___y_3612_);
v___x_3637_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3636_, v___y_3612_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___x_3636_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_self_3639_; lean_object* v_root_3640_; lean_object* v_congr_3641_; lean_object* v_target_x3f_3642_; lean_object* v_proof_x3f_3643_; uint8_t v_flipped_3644_; lean_object* v_size_3645_; uint8_t v_interpreted_3646_; uint8_t v_ctor_3647_; uint8_t v_hasLambdas_3648_; uint8_t v_heqProofs_3649_; lean_object* v_idx_3650_; lean_object* v_generation_3651_; lean_object* v_mt_3652_; lean_object* v_sTerms_3653_; uint8_t v_funCC_3654_; lean_object* v_ematchDiagSource_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3684_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_self_3639_ = lean_ctor_get(v_a_3638_, 0);
v_root_3640_ = lean_ctor_get(v_a_3638_, 2);
v_congr_3641_ = lean_ctor_get(v_a_3638_, 3);
v_target_x3f_3642_ = lean_ctor_get(v_a_3638_, 4);
v_proof_x3f_3643_ = lean_ctor_get(v_a_3638_, 5);
v_flipped_3644_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12);
v_size_3645_ = lean_ctor_get(v_a_3638_, 6);
v_interpreted_3646_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12 + 1);
v_ctor_3647_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12 + 2);
v_hasLambdas_3648_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12 + 3);
v_heqProofs_3649_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12 + 4);
v_idx_3650_ = lean_ctor_get(v_a_3638_, 7);
v_generation_3651_ = lean_ctor_get(v_a_3638_, 8);
v_mt_3652_ = lean_ctor_get(v_a_3638_, 9);
v_sTerms_3653_ = lean_ctor_get(v_a_3638_, 10);
v_funCC_3654_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3655_ = lean_ctor_get(v_a_3638_, 11);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_a_3638_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v_a_3638_, 1);
lean_dec(v_unused_3685_);
v___x_3657_ = v_a_3638_;
v_isShared_3658_ = v_isSharedCheck_3684_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_ematchDiagSource_3655_);
lean_inc(v_sTerms_3653_);
lean_inc(v_mt_3652_);
lean_inc(v_generation_3651_);
lean_inc(v_idx_3650_);
lean_inc(v_size_3645_);
lean_inc(v_proof_x3f_3643_);
lean_inc(v_target_x3f_3642_);
lean_inc(v_congr_3641_);
lean_inc(v_root_3640_);
lean_inc(v_self_3639_);
lean_dec(v_a_3638_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3684_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v_self_3659_; lean_object* v_next_3660_; lean_object* v_root_3661_; lean_object* v_congr_3662_; lean_object* v_target_x3f_3663_; lean_object* v_proof_x3f_3664_; uint8_t v_flipped_3665_; lean_object* v_size_3666_; uint8_t v_interpreted_3667_; uint8_t v_ctor_3668_; uint8_t v_hasLambdas_3669_; uint8_t v_heqProofs_3670_; lean_object* v_idx_3671_; lean_object* v_generation_3672_; lean_object* v_mt_3673_; lean_object* v_sTerms_3674_; uint8_t v_funCC_3675_; lean_object* v_ematchDiagSource_3676_; lean_object* v___x_3678_; 
v_self_3659_ = lean_ctor_get(v_rhsRoot_3443_, 0);
v_next_3660_ = lean_ctor_get(v_rhsRoot_3443_, 1);
v_root_3661_ = lean_ctor_get(v_rhsRoot_3443_, 2);
v_congr_3662_ = lean_ctor_get(v_rhsRoot_3443_, 3);
v_target_x3f_3663_ = lean_ctor_get(v_rhsRoot_3443_, 4);
v_proof_x3f_3664_ = lean_ctor_get(v_rhsRoot_3443_, 5);
v_flipped_3665_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12);
v_size_3666_ = lean_ctor_get(v_rhsRoot_3443_, 6);
v_interpreted_3667_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12 + 1);
v_ctor_3668_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12 + 2);
v_hasLambdas_3669_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12 + 3);
v_heqProofs_3670_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12 + 4);
v_idx_3671_ = lean_ctor_get(v_rhsRoot_3443_, 7);
v_generation_3672_ = lean_ctor_get(v_rhsRoot_3443_, 8);
v_mt_3673_ = lean_ctor_get(v_rhsRoot_3443_, 9);
v_sTerms_3674_ = lean_ctor_get(v_rhsRoot_3443_, 10);
v_funCC_3675_ = lean_ctor_get_uint8(v_rhsRoot_3443_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3676_ = lean_ctor_get(v_rhsRoot_3443_, 11);
lean_inc_ref(v_next_3660_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 1, v_next_3660_);
v___x_3678_ = v___x_3657_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_self_3639_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_next_3660_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v_root_3640_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v_congr_3641_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v_target_x3f_3642_);
lean_ctor_set(v_reuseFailAlloc_3683_, 5, v_proof_x3f_3643_);
lean_ctor_set(v_reuseFailAlloc_3683_, 6, v_size_3645_);
lean_ctor_set(v_reuseFailAlloc_3683_, 7, v_idx_3650_);
lean_ctor_set(v_reuseFailAlloc_3683_, 8, v_generation_3651_);
lean_ctor_set(v_reuseFailAlloc_3683_, 9, v_mt_3652_);
lean_ctor_set(v_reuseFailAlloc_3683_, 10, v_sTerms_3653_);
lean_ctor_set(v_reuseFailAlloc_3683_, 11, v_ematchDiagSource_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12, v_flipped_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12 + 1, v_interpreted_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12 + 2, v_ctor_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12 + 3, v_hasLambdas_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12 + 4, v_heqProofs_3649_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, sizeof(void*)*12 + 5, v_funCC_3654_);
v___x_3678_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3621_, v___x_3678_, v___y_3624_);
if (lean_obj_tag(v___x_3679_) == 0)
{
uint8_t v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref_known(v___x_3679_, 1);
v___x_3680_ = 0;
v___x_3681_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3635_, v_lhs_3438_, v___x_3680_);
lean_dec(v___x_3635_);
v___x_3682_ = lean_nat_add(v_size_3666_, v___y_3620_);
lean_dec(v___y_3620_);
if (v_hasLambdas_3669_ == 0)
{
lean_inc_ref(v_root_3661_);
lean_inc(v_proof_x3f_3664_);
lean_inc(v_ematchDiagSource_3676_);
lean_inc(v_generation_3672_);
lean_inc_ref(v_self_3659_);
lean_inc(v_idx_3671_);
lean_inc_ref(v_congr_3662_);
lean_inc(v_target_x3f_3663_);
lean_inc(v_mt_3673_);
lean_inc(v_sTerms_3674_);
v___y_3574_ = v_flipped_3665_;
v___y_3575_ = v___y_3612_;
v___y_3576_ = v_interpreted_3667_;
v___y_3577_ = v___y_3617_;
v___y_3578_ = v___y_3624_;
v___y_3579_ = v___y_3630_;
v___y_3580_ = v_sTerms_3674_;
v___y_3581_ = v___y_3627_;
v___y_3582_ = v_funCC_3675_;
v___y_3583_ = v_mt_3673_;
v___y_3584_ = v___y_3613_;
v___y_3585_ = v___y_3614_;
v___y_3586_ = v_target_x3f_3663_;
v___y_3587_ = v___x_3681_;
v___y_3588_ = v___y_3631_;
v___y_3589_ = v___y_3629_;
v___y_3590_ = v___y_3626_;
v___y_3591_ = v___y_3623_;
v___y_3592_ = v_heqProofs_3670_;
v___y_3593_ = v_congr_3662_;
v___y_3594_ = v___y_3633_;
v___y_3595_ = v_idx_3671_;
v___y_3596_ = v___x_3682_;
v___y_3597_ = v___y_3615_;
v___y_3598_ = v___y_3619_;
v___y_3599_ = v___y_3625_;
v___y_3600_ = v_self_3659_;
v___y_3601_ = v_generation_3672_;
v___y_3602_ = v_ctor_3668_;
v___y_3603_ = v_ematchDiagSource_3676_;
v___y_3604_ = v_proof_x3f_3664_;
v___y_3605_ = v___y_3618_;
v___y_3606_ = v___y_3632_;
v___y_3607_ = v_root_3661_;
v___y_3608_ = v___y_3628_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v___y_3616_;
goto v___jp_3573_;
}
else
{
lean_inc_ref(v_root_3661_);
lean_inc(v_proof_x3f_3664_);
lean_inc(v_ematchDiagSource_3676_);
lean_inc(v_generation_3672_);
lean_inc_ref(v_self_3659_);
lean_inc(v_idx_3671_);
lean_inc_ref(v_congr_3662_);
lean_inc(v_target_x3f_3663_);
lean_inc(v_mt_3673_);
lean_inc(v_sTerms_3674_);
v___y_3574_ = v_flipped_3665_;
v___y_3575_ = v___y_3612_;
v___y_3576_ = v_interpreted_3667_;
v___y_3577_ = v___y_3617_;
v___y_3578_ = v___y_3624_;
v___y_3579_ = v___y_3630_;
v___y_3580_ = v_sTerms_3674_;
v___y_3581_ = v___y_3627_;
v___y_3582_ = v_funCC_3675_;
v___y_3583_ = v_mt_3673_;
v___y_3584_ = v___y_3613_;
v___y_3585_ = v___y_3614_;
v___y_3586_ = v_target_x3f_3663_;
v___y_3587_ = v___x_3681_;
v___y_3588_ = v___y_3631_;
v___y_3589_ = v___y_3629_;
v___y_3590_ = v___y_3626_;
v___y_3591_ = v___y_3623_;
v___y_3592_ = v_heqProofs_3670_;
v___y_3593_ = v_congr_3662_;
v___y_3594_ = v___y_3633_;
v___y_3595_ = v_idx_3671_;
v___y_3596_ = v___x_3682_;
v___y_3597_ = v___y_3615_;
v___y_3598_ = v___y_3619_;
v___y_3599_ = v___y_3625_;
v___y_3600_ = v_self_3659_;
v___y_3601_ = v_generation_3672_;
v___y_3602_ = v_ctor_3668_;
v___y_3603_ = v_ematchDiagSource_3676_;
v___y_3604_ = v_proof_x3f_3664_;
v___y_3605_ = v___y_3618_;
v___y_3606_ = v___y_3632_;
v___y_3607_ = v_root_3661_;
v___y_3608_ = v___y_3628_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v_hasLambdas_3669_;
goto v___jp_3573_;
}
}
else
{
lean_dec(v___x_3635_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec(v___x_3635_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
v_a_3686_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3637_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3637_);
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
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
return v___x_3634_;
}
}
v___jp_3699_:
{
lean_object* v_self_3715_; lean_object* v_next_3716_; lean_object* v_size_3717_; uint8_t v_hasLambdas_3718_; uint8_t v_heqProofs_3719_; lean_object* v___x_3720_; 
v_self_3715_ = lean_ctor_get(v_lhsRoot_3442_, 0);
v_next_3716_ = lean_ctor_get(v_lhsRoot_3442_, 1);
v_size_3717_ = lean_ctor_get(v_lhsRoot_3442_, 6);
v_hasLambdas_3718_ = lean_ctor_get_uint8(v_lhsRoot_3442_, sizeof(void*)*12 + 3);
v_heqProofs_3719_ = lean_ctor_get_uint8(v_lhsRoot_3442_, sizeof(void*)*12 + 4);
v___x_3720_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3715_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v_root_3722_; lean_object* v___x_3723_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v_root_3722_ = lean_ctor_get(v_rhsNode_3441_, 2);
lean_inc_ref_n(v_root_3722_, 2);
lean_dec_ref(v_rhsNode_3441_);
lean_inc_ref(v_lhs_3438_);
v___x_3723_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3438_, v_root_3722_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_toCold_3724_; lean_object* v_options_3725_; uint8_t v_hasTrace_3726_; 
lean_dec_ref_known(v___x_3723_, 1);
v_toCold_3724_ = lean_ctor_get(v___y_3713_, 0);
v_options_3725_ = lean_ctor_get(v_toCold_3724_, 2);
v_hasTrace_3726_ = lean_ctor_get_uint8(v_options_3725_, sizeof(void*)*1);
if (v_hasTrace_3726_ == 0)
{
lean_inc(v_size_3717_);
lean_inc_ref(v_next_3716_);
lean_inc_ref(v_self_3715_);
v___y_3612_ = v_self_3715_;
v___y_3613_ = v_root_3722_;
v___y_3614_ = v_heqProofs_3719_;
v___y_3615_ = v___y_3700_;
v___y_3616_ = v_hasLambdas_3718_;
v___y_3617_ = v_fns_u2082_3704_;
v___y_3618_ = v___y_3701_;
v___y_3619_ = v_next_3716_;
v___y_3620_ = v_size_3717_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v_a_3721_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
goto v___jp_3611_;
}
else
{
lean_object* v_inheritedTraceOptions_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_inheritedTraceOptions_3727_ = lean_ctor_get(v_toCold_3724_, 11);
v___x_3728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3727_, v_options_3725_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_inc(v_size_3717_);
lean_inc_ref(v_next_3716_);
lean_inc_ref(v_self_3715_);
v___y_3612_ = v_self_3715_;
v___y_3613_ = v_root_3722_;
v___y_3614_ = v_heqProofs_3719_;
v___y_3615_ = v___y_3700_;
v___y_3616_ = v_hasLambdas_3718_;
v___y_3617_ = v_fns_u2082_3704_;
v___y_3618_ = v___y_3701_;
v___y_3619_ = v_next_3716_;
v___y_3620_ = v_size_3717_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v_a_3721_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
goto v___jp_3611_;
}
else
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Meta_Grind_updateLastTag(v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v___x_3731_; 
lean_dec_ref_known(v___x_3730_, 1);
lean_inc_ref(v_lhs_3438_);
v___x_3731_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3438_, v___y_3705_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
lean_inc_ref(v_root_3722_);
v___x_3733_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3722_, v___y_3705_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = lean_st_ref_get(v___y_3705_);
lean_inc_ref(v_lhs_3438_);
v___x_3736_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3735_, v_lhs_3438_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___x_3735_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3738_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v___x_3738_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3737_, v___y_3705_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3732_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v_a_3734_);
v___x_3743_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v_a_3739_);
v___x_3746_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3698_, v___x_3745_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_dec_ref_known(v___x_3746_, 1);
lean_inc(v_size_3717_);
lean_inc_ref(v_next_3716_);
lean_inc_ref(v_self_3715_);
v___y_3612_ = v_self_3715_;
v___y_3613_ = v_root_3722_;
v___y_3614_ = v_heqProofs_3719_;
v___y_3615_ = v___y_3700_;
v___y_3616_ = v_hasLambdas_3718_;
v___y_3617_ = v_fns_u2082_3704_;
v___y_3618_ = v___y_3701_;
v___y_3619_ = v_next_3716_;
v___y_3620_ = v_size_3717_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v_a_3721_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
goto v___jp_3611_;
}
else
{
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
return v___x_3746_;
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3734_);
lean_dec(v_a_3732_);
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
v_a_3747_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3738_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3738_);
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
lean_dec(v_a_3734_);
lean_dec(v_a_3732_);
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
v_a_3755_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3736_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3736_);
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
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3732_);
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
v_a_3763_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3733_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3733_);
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
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
v_a_3771_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3731_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3731_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
return v___x_3730_;
}
}
}
}
else
{
lean_dec_ref(v_root_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_lhs_3438_);
return v___x_3723_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_fns_u2082_3704_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
v_a_3779_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3720_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3720_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
v___jp_3787_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3802_ = lean_array_get_size(v___y_3790_);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_nat_dec_eq(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v_self_3805_; lean_object* v___x_3806_; 
v_self_3805_ = lean_ctor_get(v_lhsRoot_3442_, 0);
lean_inc_ref(v_self_3805_);
v___x_3806_ = l_Lean_Meta_Grind_getFnRoots(v_self_3805_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___y_3700_ = v___y_3788_;
v___y_3701_ = v_fns_u2081_3791_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v_fns_u2082_3704_ = v_a_3807_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
goto v___jp_3699_;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_fns_u2081_3791_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
v_a_3808_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3806_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3700_ = v___y_3788_;
v___y_3701_ = v_fns_u2081_3791_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v_fns_u2082_3704_ = v___x_3816_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
goto v___jp_3699_;
}
}
v___jp_3817_:
{
lean_object* v___x_3828_; 
lean_inc_ref(v_lhs_3438_);
v___x_3828_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3438_, v___y_3818_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3896_; 
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v___x_3828_, 0);
lean_dec(v_unused_3897_);
v___x_3830_ = v___x_3828_;
v_isShared_3831_ = v_isSharedCheck_3896_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v___x_3828_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3896_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_self_3832_; lean_object* v_next_3833_; lean_object* v_root_3834_; lean_object* v_congr_3835_; lean_object* v_size_3836_; uint8_t v_interpreted_3837_; uint8_t v_ctor_3838_; uint8_t v_hasLambdas_3839_; uint8_t v_heqProofs_3840_; lean_object* v_idx_3841_; lean_object* v_generation_3842_; lean_object* v_mt_3843_; lean_object* v_sTerms_3844_; uint8_t v_funCC_3845_; lean_object* v_ematchDiagSource_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3893_; 
v_self_3832_ = lean_ctor_get(v_lhsNode_3440_, 0);
v_next_3833_ = lean_ctor_get(v_lhsNode_3440_, 1);
v_root_3834_ = lean_ctor_get(v_lhsNode_3440_, 2);
v_congr_3835_ = lean_ctor_get(v_lhsNode_3440_, 3);
v_size_3836_ = lean_ctor_get(v_lhsNode_3440_, 6);
v_interpreted_3837_ = lean_ctor_get_uint8(v_lhsNode_3440_, sizeof(void*)*12 + 1);
v_ctor_3838_ = lean_ctor_get_uint8(v_lhsNode_3440_, sizeof(void*)*12 + 2);
v_hasLambdas_3839_ = lean_ctor_get_uint8(v_lhsNode_3440_, sizeof(void*)*12 + 3);
v_heqProofs_3840_ = lean_ctor_get_uint8(v_lhsNode_3440_, sizeof(void*)*12 + 4);
v_idx_3841_ = lean_ctor_get(v_lhsNode_3440_, 7);
v_generation_3842_ = lean_ctor_get(v_lhsNode_3440_, 8);
v_mt_3843_ = lean_ctor_get(v_lhsNode_3440_, 9);
v_sTerms_3844_ = lean_ctor_get(v_lhsNode_3440_, 10);
v_funCC_3845_ = lean_ctor_get_uint8(v_lhsNode_3440_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3846_ = lean_ctor_get(v_lhsNode_3440_, 11);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_lhsNode_3440_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; lean_object* v_unused_3895_; 
v_unused_3894_ = lean_ctor_get(v_lhsNode_3440_, 5);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_lhsNode_3440_, 4);
lean_dec(v_unused_3895_);
v___x_3848_ = v_lhsNode_3440_;
v_isShared_3849_ = v_isSharedCheck_3893_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_ematchDiagSource_3846_);
lean_inc(v_sTerms_3844_);
lean_inc(v_mt_3843_);
lean_inc(v_generation_3842_);
lean_inc(v_idx_3841_);
lean_inc(v_size_3836_);
lean_inc(v_congr_3835_);
lean_inc(v_root_3834_);
lean_inc(v_next_3833_);
lean_inc(v_self_3832_);
lean_dec(v_lhsNode_3440_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3893_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set_tag(v___x_3830_, 1);
lean_ctor_set(v___x_3830_, 0, v_rhs_3439_);
v___x_3851_ = v___x_3830_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_rhs_3439_);
v___x_3851_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_proof_3436_);
lean_inc_ref(v_root_3834_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 5, v___x_3852_);
lean_ctor_set(v___x_3848_, 4, v___x_3851_);
v___x_3854_ = v___x_3848_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_self_3832_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_next_3833_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_root_3834_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_congr_3835_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3891_, 5, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3891_, 6, v_size_3836_);
lean_ctor_set(v_reuseFailAlloc_3891_, 7, v_idx_3841_);
lean_ctor_set(v_reuseFailAlloc_3891_, 8, v_generation_3842_);
lean_ctor_set(v_reuseFailAlloc_3891_, 9, v_mt_3843_);
lean_ctor_set(v_reuseFailAlloc_3891_, 10, v_sTerms_3844_);
lean_ctor_set(v_reuseFailAlloc_3891_, 11, v_ematchDiagSource_3846_);
lean_ctor_set_uint8(v_reuseFailAlloc_3891_, sizeof(void*)*12 + 1, v_interpreted_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3891_, sizeof(void*)*12 + 2, v_ctor_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3891_, sizeof(void*)*12 + 3, v_hasLambdas_3839_);
lean_ctor_set_uint8(v_reuseFailAlloc_3891_, sizeof(void*)*12 + 4, v_heqProofs_3840_);
lean_ctor_set_uint8(v_reuseFailAlloc_3891_, sizeof(void*)*12 + 5, v_funCC_3845_);
v___x_3854_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*12, v_flipped_3444_);
lean_inc_ref(v_lhs_3438_);
v___x_3855_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3438_, v___x_3854_, v___y_3818_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref_known(v___x_3855_, 1);
v___x_3856_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3442_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3443_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v___x_3860_ = lean_array_get_size(v_a_3857_);
v___x_3861_ = lean_unsigned_to_nat(0u);
v___x_3862_ = lean_nat_dec_eq(v___x_3860_, v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v_self_3863_; lean_object* v___x_3864_; 
v_self_3863_ = lean_ctor_get(v_rhsRoot_3443_, 0);
lean_inc_ref(v_self_3863_);
v___x_3864_ = l_Lean_Meta_Grind_getFnRoots(v_self_3863_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___y_3788_ = v_a_3857_;
v___y_3789_ = v_root_3834_;
v___y_3790_ = v_a_3859_;
v_fns_u2081_3791_ = v_a_3865_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
goto v___jp_3787_;
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3859_);
lean_dec(v_a_3857_);
lean_dec_ref(v_root_3834_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
v_a_3866_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3864_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v___x_3874_; 
v___x_3874_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3788_ = v_a_3857_;
v___y_3789_ = v_root_3834_;
v___y_3790_ = v_a_3859_;
v_fns_u2081_3791_ = v___x_3874_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
goto v___jp_3787_;
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_a_3857_);
lean_dec_ref(v_root_3834_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
v_a_3875_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3858_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3858_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_root_3834_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
v_a_3883_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3856_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3856_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_dec_ref(v_root_3834_);
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhs_3438_);
return v___x_3855_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3443_);
lean_dec_ref(v_lhsRoot_3442_);
lean_dec_ref(v_rhsNode_3441_);
lean_dec_ref(v_lhsNode_3440_);
lean_dec_ref(v_rhs_3439_);
lean_dec_ref(v_lhs_3438_);
lean_dec_ref(v_proof_3436_);
return v___x_3828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3927_ = _args[0];
lean_object* v_isHEq_3928_ = _args[1];
lean_object* v_lhs_3929_ = _args[2];
lean_object* v_rhs_3930_ = _args[3];
lean_object* v_lhsNode_3931_ = _args[4];
lean_object* v_rhsNode_3932_ = _args[5];
lean_object* v_lhsRoot_3933_ = _args[6];
lean_object* v_rhsRoot_3934_ = _args[7];
lean_object* v_flipped_3935_ = _args[8];
lean_object* v_a_3936_ = _args[9];
lean_object* v_a_3937_ = _args[10];
lean_object* v_a_3938_ = _args[11];
lean_object* v_a_3939_ = _args[12];
lean_object* v_a_3940_ = _args[13];
lean_object* v_a_3941_ = _args[14];
lean_object* v_a_3942_ = _args[15];
lean_object* v_a_3943_ = _args[16];
lean_object* v_a_3944_ = _args[17];
lean_object* v_a_3945_ = _args[18];
lean_object* v_a_3946_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3947_; uint8_t v_flipped_boxed_3948_; lean_object* v_res_3949_; 
v_isHEq_boxed_3947_ = lean_unbox(v_isHEq_3928_);
v_flipped_boxed_3948_ = lean_unbox(v_flipped_3935_);
v_res_3949_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3927_, v_isHEq_boxed_3947_, v_lhs_3929_, v_rhs_3930_, v_lhsNode_3931_, v_rhsNode_3932_, v_lhsRoot_3933_, v_rhsRoot_3934_, v_flipped_boxed_3948_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec(v_a_3936_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3950_, lean_object* v_as_x27_3951_, lean_object* v_b_3952_, lean_object* v_a_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3951_, v_b_3952_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3966_, lean_object* v_as_x27_3967_, lean_object* v_b_3968_, lean_object* v_a_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3966_, v_as_x27_3967_, v_b_3968_, v_a_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec(v_as_x27_3967_);
lean_dec(v_as_3966_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3982_, lean_object* v_as_x27_3983_, lean_object* v_b_3984_, lean_object* v_a_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3983_, v_b_3984_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3998_, lean_object* v_as_x27_3999_, lean_object* v_b_4000_, lean_object* v_a_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3998_, v_as_x27_3999_, v_b_4000_, v_a_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec(v_as_x27_3999_);
lean_dec(v_as_3998_);
return v_res_4013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4016_ = l_Lean_stringToMessageData(v___x_4015_);
return v___x_4016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4022_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4023_ = l_Lean_Name_append(v___x_4022_, v___x_4021_);
return v___x_4023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4026_ = l_Lean_stringToMessageData(v___x_4025_);
return v___x_4026_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4029_ = l_Lean_stringToMessageData(v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4030_, lean_object* v_rhs_4031_, lean_object* v_proof_4032_, uint8_t v_isHEq_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_st_ref_get(v_a_4034_);
lean_inc_ref(v_lhs_4030_);
v___x_4049_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4048_, v_lhs_4030_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v___x_4048_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = lean_st_ref_get(v_a_4034_);
lean_inc_ref(v_rhs_4031_);
v___x_4052_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4051_, v_rhs_4031_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec(v___x_4051_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v_root_4054_; lean_object* v_root_4055_; size_t v___x_4056_; size_t v___x_4057_; uint8_t v___x_4058_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4052_, 1);
v_root_4054_ = lean_ctor_get(v_a_4050_, 2);
v_root_4055_ = lean_ctor_get(v_a_4053_, 2);
v___x_4056_ = lean_ptr_addr(v_root_4054_);
v___x_4057_ = lean_ptr_addr(v_root_4055_);
v___x_4058_ = lean_usize_dec_eq(v___x_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v_toCold_4059_; lean_object* v_options_4060_; lean_object* v_inheritedTraceOptions_4061_; uint8_t v_hasTrace_4062_; uint8_t v___x_4063_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4101_; uint8_t v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4129_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4159_; uint8_t v___y_4160_; uint8_t v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4191_; uint8_t v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; uint8_t v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; uint8_t v___y_4218_; lean_object* v___y_4219_; lean_object* v_size_4220_; uint8_t v_interpreted_4221_; uint8_t v_ctor_4222_; lean_object* v___y_4223_; lean_object* v___y_4227_; uint8_t v_ctor_4228_; uint8_t v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4249_; lean_object* v___y_4250_; uint8_t v_valueInconsistency_4251_; uint8_t v_trueEqFalse_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; uint8_t v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; 
v_toCold_4059_ = lean_ctor_get(v_a_4042_, 0);
v_options_4060_ = lean_ctor_get(v_toCold_4059_, 2);
v_inheritedTraceOptions_4061_ = lean_ctor_get(v_toCold_4059_, 11);
v_hasTrace_4062_ = lean_ctor_get_uint8(v_options_4060_, sizeof(void*)*1);
v___x_4063_ = 1;
if (v_hasTrace_4062_ == 0)
{
v___y_4309_ = v_a_4034_;
v___y_4310_ = v_a_4035_;
v___y_4311_ = v_a_4036_;
v___y_4312_ = v_a_4037_;
v___y_4313_ = v_a_4038_;
v___y_4314_ = v_a_4039_;
v___y_4315_ = v_a_4040_;
v___y_4316_ = v_a_4041_;
v___y_4317_ = v_a_4042_;
v___y_4318_ = v_a_4043_;
goto v___jp_4308_;
}
else
{
lean_object* v___x_4352_; lean_object* v_____do__lift_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v___x_4352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4368_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4061_, v_options_4060_, v___x_4367_);
if (v___x_4368_ == 0)
{
v___y_4309_ = v_a_4034_;
v___y_4310_ = v_a_4035_;
v___y_4311_ = v_a_4036_;
v___y_4312_ = v_a_4037_;
v___y_4313_ = v_a_4038_;
v___y_4314_ = v_a_4039_;
v___y_4315_ = v_a_4040_;
v___y_4316_ = v_a_4041_;
v___y_4317_ = v_a_4042_;
v___y_4318_ = v_a_4043_;
goto v___jp_4308_;
}
else
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Meta_Grind_updateLastTag(v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_dec_ref_known(v___x_4369_, 1);
if (v_isHEq_4033_ == 0)
{
lean_object* v___x_4370_; 
lean_inc_ref(v_rhs_4031_);
lean_inc_ref(v_lhs_4030_);
v___x_4370_ = l_Lean_Meta_mkEq(v_lhs_4030_, v_rhs_4031_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4370_, 1);
v_____do__lift_4354_ = v_a_4371_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
v___y_4359_ = v_a_4038_;
v___y_4360_ = v_a_4039_;
v___y_4361_ = v_a_4040_;
v___y_4362_ = v_a_4041_;
v___y_4363_ = v_a_4042_;
v___y_4364_ = v_a_4043_;
goto v___jp_4353_;
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4372_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4370_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4370_);
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
lean_object* v___x_4380_; 
lean_inc_ref(v_rhs_4031_);
lean_inc_ref(v_lhs_4030_);
v___x_4380_ = l_Lean_Meta_mkHEq(v_lhs_4030_, v_rhs_4031_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4380_, 1);
v_____do__lift_4354_ = v_a_4381_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
v___y_4359_ = v_a_4038_;
v___y_4360_ = v_a_4039_;
v___y_4361_ = v_a_4040_;
v___y_4362_ = v_a_4041_;
v___y_4363_ = v_a_4042_;
v___y_4364_ = v_a_4043_;
goto v___jp_4353_;
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4382_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4380_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4380_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
else
{
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
return v___x_4369_;
}
}
v___jp_4353_:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = l_Lean_MessageData_ofExpr(v_____do__lift_4354_);
v___x_4366_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4352_, v___x_4365_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_dec_ref_known(v___x_4366_, 1);
v___y_4309_ = v___y_4355_;
v___y_4310_ = v___y_4356_;
v___y_4311_ = v___y_4357_;
v___y_4312_ = v___y_4358_;
v___y_4313_ = v___y_4359_;
v___y_4314_ = v___y_4360_;
v___y_4315_ = v___y_4361_;
v___y_4316_ = v___y_4362_;
v___y_4317_ = v___y_4363_;
v___y_4318_ = v___y_4364_;
goto v___jp_4308_;
}
else
{
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
return v___x_4366_;
}
}
}
v___jp_4064_:
{
lean_object* v_toCold_4075_; lean_object* v_options_4076_; uint8_t v_hasTrace_4077_; 
v_toCold_4075_ = lean_ctor_get(v___y_4073_, 0);
v_options_4076_ = lean_ctor_get(v_toCold_4075_, 2);
v_hasTrace_4077_ = lean_ctor_get_uint8(v_options_4076_, sizeof(void*)*1);
if (v_hasTrace_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Meta_Grind_checkInvariants(v___x_4058_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
return v___x_4078_;
}
else
{
lean_object* v_inheritedTraceOptions_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
v_inheritedTraceOptions_4079_ = lean_ctor_get(v_toCold_4075_, 11);
v___x_4080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4079_, v_options_4076_, v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Meta_Grind_checkInvariants(v___x_4058_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
return v___x_4083_;
}
else
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Meta_Grind_updateLastTag(v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_dec_ref_known(v___x_4084_, 1);
v___x_4085_ = lean_st_ref_get(v___y_4065_);
v___x_4086_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4085_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___x_4085_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v_a_4087_);
v___x_4090_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4080_, v___x_4089_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v___x_4091_; 
lean_dec_ref_known(v___x_4090_, 1);
v___x_4091_ = l_Lean_Meta_Grind_checkInvariants(v___x_4058_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
return v___x_4091_;
}
else
{
return v___x_4090_;
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
v_a_4092_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4086_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4086_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
return v___x_4084_;
}
}
}
}
v___jp_4100_:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4104_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; uint8_t v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref_known(v___x_4114_, 1);
v___x_4116_ = lean_unbox(v_a_4115_);
lean_dec(v_a_4115_);
if (v___x_4116_ == 0)
{
if (v___y_4102_ == 0)
{
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4101_);
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
goto v___jp_4064_;
}
else
{
lean_object* v_self_4117_; lean_object* v_self_4118_; lean_object* v___x_4119_; 
v_self_4117_ = lean_ctor_get(v___y_4101_, 0);
lean_inc_ref(v_self_4117_);
lean_dec_ref(v___y_4101_);
v_self_4118_ = lean_ctor_get(v___y_4103_, 0);
lean_inc_ref(v_self_4118_);
lean_dec_ref(v___y_4103_);
v___x_4119_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4117_, v_self_4118_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_dec_ref_known(v___x_4119_, 1);
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
goto v___jp_4064_;
}
else
{
return v___x_4119_;
}
}
}
else
{
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4101_);
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
goto v___jp_4064_;
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4101_);
v_a_4120_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4114_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4114_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
v___jp_4128_:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4132_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; uint8_t v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = lean_unbox(v_a_4143_);
lean_dec(v_a_4143_);
if (v___x_4144_ == 0)
{
uint8_t v_ctor_4145_; 
v_ctor_4145_ = lean_ctor_get_uint8(v___y_4129_, sizeof(void*)*12 + 2);
if (v_ctor_4145_ == 0)
{
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
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
goto v___jp_4100_;
}
else
{
uint8_t v_ctor_4146_; 
v_ctor_4146_ = lean_ctor_get_uint8(v___y_4131_, sizeof(void*)*12 + 2);
if (v_ctor_4146_ == 0)
{
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
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
goto v___jp_4100_;
}
else
{
lean_object* v_self_4147_; lean_object* v_self_4148_; lean_object* v___x_4149_; 
v_self_4147_ = lean_ctor_get(v___y_4129_, 0);
v_self_4148_ = lean_ctor_get(v___y_4131_, 0);
lean_inc_ref(v_self_4148_);
lean_inc_ref(v_self_4147_);
v___x_4149_ = l_Lean_Meta_Grind_propagateCtor(v_self_4147_, v_self_4148_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_dec_ref_known(v___x_4149_, 1);
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
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
goto v___jp_4100_;
}
else
{
lean_dec_ref(v___y_4131_);
lean_dec_ref(v___y_4129_);
return v___x_4149_;
}
}
}
}
else
{
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
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
goto v___jp_4100_;
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___y_4131_);
lean_dec_ref(v___y_4129_);
v_a_4150_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4142_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4142_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
v___jp_4158_:
{
if (v___y_4160_ == 0)
{
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
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
goto v___jp_4128_;
}
else
{
lean_object* v___x_4173_; 
v___x_4173_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_dec_ref_known(v___x_4173_, 1);
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
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
goto v___jp_4128_;
}
else
{
lean_dec_ref(v___y_4162_);
lean_dec_ref(v___y_4159_);
return v___x_4173_;
}
}
}
v___jp_4174_:
{
lean_object* v___x_4189_; 
lean_inc_ref(v___y_4175_);
lean_inc_ref(v___y_4187_);
v___x_4189_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4032_, v_isHEq_4033_, v_rhs_4031_, v_lhs_4030_, v_a_4053_, v_a_4050_, v___y_4187_, v___y_4175_, v___x_4063_, v___y_4179_, v___y_4184_, v___y_4182_, v___y_4177_, v___y_4181_, v___y_4180_, v___y_4178_, v___y_4188_, v___y_4183_, v___y_4186_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref_known(v___x_4189_, 1);
v___y_4159_ = v___y_4175_;
v___y_4160_ = v___y_4176_;
v___y_4161_ = v___y_4185_;
v___y_4162_ = v___y_4187_;
v___y_4163_ = v___y_4179_;
v___y_4164_ = v___y_4184_;
v___y_4165_ = v___y_4182_;
v___y_4166_ = v___y_4177_;
v___y_4167_ = v___y_4181_;
v___y_4168_ = v___y_4180_;
v___y_4169_ = v___y_4178_;
v___y_4170_ = v___y_4188_;
v___y_4171_ = v___y_4183_;
v___y_4172_ = v___y_4186_;
goto v___jp_4158_;
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
lean_object* v___x_4205_; 
lean_inc_ref(v___y_4203_);
lean_inc_ref(v___y_4191_);
v___x_4205_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4032_, v_isHEq_4033_, v_lhs_4030_, v_rhs_4031_, v_a_4050_, v_a_4053_, v___y_4191_, v___y_4203_, v___x_4058_, v___y_4195_, v___y_4200_, v___y_4198_, v___y_4193_, v___y_4197_, v___y_4196_, v___y_4194_, v___y_4204_, v___y_4199_, v___y_4202_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_dec_ref_known(v___x_4205_, 1);
v___y_4159_ = v___y_4191_;
v___y_4160_ = v___y_4192_;
v___y_4161_ = v___y_4201_;
v___y_4162_ = v___y_4203_;
v___y_4163_ = v___y_4195_;
v___y_4164_ = v___y_4200_;
v___y_4165_ = v___y_4198_;
v___y_4166_ = v___y_4193_;
v___y_4167_ = v___y_4197_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4194_;
v___y_4170_ = v___y_4204_;
v___y_4171_ = v___y_4199_;
v___y_4172_ = v___y_4202_;
goto v___jp_4158_;
}
else
{
lean_dec_ref(v___y_4203_);
lean_dec_ref(v___y_4191_);
return v___x_4205_;
}
}
v___jp_4206_:
{
lean_object* v_size_4224_; uint8_t v___x_4225_; 
v_size_4224_ = lean_ctor_get(v___y_4207_, 6);
v___x_4225_ = lean_nat_dec_lt(v_size_4220_, v_size_4224_);
lean_dec(v_size_4220_);
if (v___x_4225_ == 0)
{
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4217_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4223_;
goto v___jp_4190_;
}
else
{
if (v_interpreted_4221_ == 0)
{
if (v_ctor_4222_ == 0)
{
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4208_;
v___y_4177_ = v___y_4209_;
v___y_4178_ = v___y_4210_;
v___y_4179_ = v___y_4211_;
v___y_4180_ = v___y_4212_;
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4215_;
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4218_;
v___y_4186_ = v___y_4217_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4223_;
goto v___jp_4174_;
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
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4217_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4223_;
goto v___jp_4190_;
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
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4217_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4223_;
goto v___jp_4190_;
}
}
}
v___jp_4226_:
{
if (v_ctor_4228_ == 0)
{
lean_object* v_size_4242_; uint8_t v_interpreted_4243_; uint8_t v_ctor_4244_; 
v_size_4242_ = lean_ctor_get(v___y_4240_, 6);
lean_inc(v_size_4242_);
v_interpreted_4243_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 1);
v_ctor_4244_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 2);
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4230_;
v___y_4210_ = v___y_4231_;
v___y_4211_ = v___y_4232_;
v___y_4212_ = v___y_4233_;
v___y_4213_ = v___y_4234_;
v___y_4214_ = v___y_4235_;
v___y_4215_ = v___y_4236_;
v___y_4216_ = v___y_4237_;
v___y_4217_ = v___y_4238_;
v___y_4218_ = v___y_4239_;
v___y_4219_ = v___y_4240_;
v_size_4220_ = v_size_4242_;
v_interpreted_4221_ = v_interpreted_4243_;
v_ctor_4222_ = v_ctor_4244_;
v___y_4223_ = v___y_4241_;
goto v___jp_4206_;
}
else
{
uint8_t v_ctor_4245_; 
v_ctor_4245_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 2);
if (v_ctor_4245_ == 0)
{
v___y_4175_ = v___y_4227_;
v___y_4176_ = v___y_4229_;
v___y_4177_ = v___y_4230_;
v___y_4178_ = v___y_4231_;
v___y_4179_ = v___y_4232_;
v___y_4180_ = v___y_4233_;
v___y_4181_ = v___y_4234_;
v___y_4182_ = v___y_4235_;
v___y_4183_ = v___y_4236_;
v___y_4184_ = v___y_4237_;
v___y_4185_ = v___y_4239_;
v___y_4186_ = v___y_4238_;
v___y_4187_ = v___y_4240_;
v___y_4188_ = v___y_4241_;
goto v___jp_4174_;
}
else
{
lean_object* v_size_4246_; uint8_t v_interpreted_4247_; 
v_size_4246_ = lean_ctor_get(v___y_4240_, 6);
lean_inc(v_size_4246_);
v_interpreted_4247_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 1);
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4230_;
v___y_4210_ = v___y_4231_;
v___y_4211_ = v___y_4232_;
v___y_4212_ = v___y_4233_;
v___y_4213_ = v___y_4234_;
v___y_4214_ = v___y_4235_;
v___y_4215_ = v___y_4236_;
v___y_4216_ = v___y_4237_;
v___y_4217_ = v___y_4238_;
v___y_4218_ = v___y_4239_;
v___y_4219_ = v___y_4240_;
v_size_4220_ = v_size_4246_;
v_interpreted_4221_ = v_interpreted_4247_;
v_ctor_4222_ = v_ctor_4245_;
v___y_4223_ = v___y_4241_;
goto v___jp_4206_;
}
}
}
v___jp_4248_:
{
uint8_t v_interpreted_4263_; 
v_interpreted_4263_ = lean_ctor_get_uint8(v___y_4249_, sizeof(void*)*12 + 1);
if (v_interpreted_4263_ == 0)
{
uint8_t v_ctor_4264_; 
v_ctor_4264_ = lean_ctor_get_uint8(v___y_4249_, sizeof(void*)*12 + 2);
v___y_4227_ = v___y_4249_;
v_ctor_4228_ = v_ctor_4264_;
v___y_4229_ = v_trueEqFalse_4252_;
v___y_4230_ = v___y_4256_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___y_4253_;
v___y_4233_ = v___y_4258_;
v___y_4234_ = v___y_4257_;
v___y_4235_ = v___y_4255_;
v___y_4236_ = v___y_4261_;
v___y_4237_ = v___y_4254_;
v___y_4238_ = v___y_4262_;
v___y_4239_ = v_valueInconsistency_4251_;
v___y_4240_ = v___y_4250_;
v___y_4241_ = v___y_4260_;
goto v___jp_4226_;
}
else
{
uint8_t v_interpreted_4265_; 
v_interpreted_4265_ = lean_ctor_get_uint8(v___y_4250_, sizeof(void*)*12 + 1);
if (v_interpreted_4265_ == 0)
{
v___y_4175_ = v___y_4249_;
v___y_4176_ = v_trueEqFalse_4252_;
v___y_4177_ = v___y_4256_;
v___y_4178_ = v___y_4259_;
v___y_4179_ = v___y_4253_;
v___y_4180_ = v___y_4258_;
v___y_4181_ = v___y_4257_;
v___y_4182_ = v___y_4255_;
v___y_4183_ = v___y_4261_;
v___y_4184_ = v___y_4254_;
v___y_4185_ = v_valueInconsistency_4251_;
v___y_4186_ = v___y_4262_;
v___y_4187_ = v___y_4250_;
v___y_4188_ = v___y_4260_;
goto v___jp_4174_;
}
else
{
uint8_t v_ctor_4266_; 
v_ctor_4266_ = lean_ctor_get_uint8(v___y_4249_, sizeof(void*)*12 + 2);
v___y_4227_ = v___y_4249_;
v_ctor_4228_ = v_ctor_4266_;
v___y_4229_ = v_trueEqFalse_4252_;
v___y_4230_ = v___y_4256_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___y_4253_;
v___y_4233_ = v___y_4258_;
v___y_4234_ = v___y_4257_;
v___y_4235_ = v___y_4255_;
v___y_4236_ = v___y_4261_;
v___y_4237_ = v___y_4254_;
v___y_4238_ = v___y_4262_;
v___y_4239_ = v_valueInconsistency_4251_;
v___y_4240_ = v___y_4250_;
v___y_4241_ = v___y_4260_;
goto v___jp_4226_;
}
}
}
v___jp_4267_:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4277_, v___y_4272_, v___y_4268_, v___y_4270_, v___y_4275_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_dec_ref_known(v___x_4280_, 1);
v___y_4249_ = v___y_4269_;
v___y_4250_ = v___y_4278_;
v_valueInconsistency_4251_ = v___x_4058_;
v_trueEqFalse_4252_ = v___x_4063_;
v___y_4253_ = v___y_4277_;
v___y_4254_ = v___y_4276_;
v___y_4255_ = v___y_4273_;
v___y_4256_ = v___y_4271_;
v___y_4257_ = v___y_4279_;
v___y_4258_ = v___y_4274_;
v___y_4259_ = v___y_4272_;
v___y_4260_ = v___y_4268_;
v___y_4261_ = v___y_4270_;
v___y_4262_ = v___y_4275_;
goto v___jp_4248_;
}
else
{
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4269_);
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
return v___x_4280_;
}
}
v___jp_4281_:
{
if (v___y_4287_ == 0)
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_Meta_Grind_hasSameType(v___y_4291_, v___y_4292_, v___y_4286_, v___y_4283_, v___y_4284_, v___y_4290_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; uint8_t v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = lean_unbox(v_a_4298_);
lean_dec(v_a_4298_);
if (v___x_4299_ == 0)
{
v___y_4249_ = v___y_4282_;
v___y_4250_ = v___y_4294_;
v_valueInconsistency_4251_ = v___x_4058_;
v_trueEqFalse_4252_ = v___x_4058_;
v___y_4253_ = v___y_4295_;
v___y_4254_ = v___y_4293_;
v___y_4255_ = v___y_4288_;
v___y_4256_ = v___y_4285_;
v___y_4257_ = v___y_4296_;
v___y_4258_ = v___y_4289_;
v___y_4259_ = v___y_4286_;
v___y_4260_ = v___y_4283_;
v___y_4261_ = v___y_4284_;
v___y_4262_ = v___y_4290_;
goto v___jp_4248_;
}
else
{
v___y_4249_ = v___y_4282_;
v___y_4250_ = v___y_4294_;
v_valueInconsistency_4251_ = v___x_4063_;
v_trueEqFalse_4252_ = v___x_4058_;
v___y_4253_ = v___y_4295_;
v___y_4254_ = v___y_4293_;
v___y_4255_ = v___y_4288_;
v___y_4256_ = v___y_4285_;
v___y_4257_ = v___y_4296_;
v___y_4258_ = v___y_4289_;
v___y_4259_ = v___y_4286_;
v___y_4260_ = v___y_4283_;
v___y_4261_ = v___y_4284_;
v___y_4262_ = v___y_4290_;
goto v___jp_4248_;
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v___y_4294_);
lean_dec_ref(v___y_4282_);
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4300_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4297_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4297_);
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
else
{
lean_dec_ref(v___y_4292_);
lean_dec_ref(v___y_4291_);
v___y_4249_ = v___y_4282_;
v___y_4250_ = v___y_4294_;
v_valueInconsistency_4251_ = v___x_4063_;
v_trueEqFalse_4252_ = v___x_4058_;
v___y_4253_ = v___y_4295_;
v___y_4254_ = v___y_4293_;
v___y_4255_ = v___y_4288_;
v___y_4256_ = v___y_4285_;
v___y_4257_ = v___y_4296_;
v___y_4258_ = v___y_4289_;
v___y_4259_ = v___y_4286_;
v___y_4260_ = v___y_4283_;
v___y_4261_ = v___y_4284_;
v___y_4262_ = v___y_4290_;
goto v___jp_4248_;
}
}
v___jp_4308_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_st_ref_get(v___y_4309_);
lean_inc_ref(v_root_4054_);
v___x_4320_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4319_, v_root_4054_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___x_4319_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4320_, 1);
v___x_4322_ = lean_st_ref_get(v___y_4309_);
lean_inc_ref(v_root_4055_);
v___x_4323_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4322_, v_root_4055_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___x_4322_);
if (lean_obj_tag(v___x_4323_) == 0)
{
uint8_t v_interpreted_4324_; 
v_interpreted_4324_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 1);
if (v_interpreted_4324_ == 0)
{
lean_object* v_a_4325_; uint8_t v_ctor_4326_; 
v_a_4325_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4323_, 1);
v_ctor_4326_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 2);
v___y_4227_ = v_a_4321_;
v_ctor_4228_ = v_ctor_4326_;
v___y_4229_ = v___x_4058_;
v___y_4230_ = v___y_4312_;
v___y_4231_ = v___y_4315_;
v___y_4232_ = v___y_4309_;
v___y_4233_ = v___y_4314_;
v___y_4234_ = v___y_4313_;
v___y_4235_ = v___y_4311_;
v___y_4236_ = v___y_4317_;
v___y_4237_ = v___y_4310_;
v___y_4238_ = v___y_4318_;
v___y_4239_ = v___x_4058_;
v___y_4240_ = v_a_4325_;
v___y_4241_ = v___y_4316_;
goto v___jp_4226_;
}
else
{
lean_object* v_a_4327_; uint8_t v_interpreted_4328_; 
v_a_4327_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4323_, 1);
v_interpreted_4328_ = lean_ctor_get_uint8(v_a_4327_, sizeof(void*)*12 + 1);
if (v_interpreted_4328_ == 0)
{
v___y_4175_ = v_a_4321_;
v___y_4176_ = v___x_4058_;
v___y_4177_ = v___y_4312_;
v___y_4178_ = v___y_4315_;
v___y_4179_ = v___y_4309_;
v___y_4180_ = v___y_4314_;
v___y_4181_ = v___y_4313_;
v___y_4182_ = v___y_4311_;
v___y_4183_ = v___y_4317_;
v___y_4184_ = v___y_4310_;
v___y_4185_ = v___x_4058_;
v___y_4186_ = v___y_4318_;
v___y_4187_ = v_a_4327_;
v___y_4188_ = v___y_4316_;
goto v___jp_4174_;
}
else
{
lean_object* v_self_4329_; uint8_t v_ctor_4330_; uint8_t v_heqProofs_4331_; lean_object* v_self_4332_; uint8_t v_heqProofs_4333_; uint8_t v___x_4334_; 
v_self_4329_ = lean_ctor_get(v_a_4321_, 0);
v_ctor_4330_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 2);
v_heqProofs_4331_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 4);
v_self_4332_ = lean_ctor_get(v_a_4327_, 0);
v_heqProofs_4333_ = lean_ctor_get_uint8(v_a_4327_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4054_);
v___x_4334_ = l_Lean_Expr_isTrue(v_root_4054_);
if (v___x_4334_ == 0)
{
uint8_t v___x_4335_; 
lean_inc_ref(v_root_4055_);
v___x_4335_ = l_Lean_Expr_isTrue(v_root_4055_);
if (v___x_4335_ == 0)
{
if (v_isHEq_4033_ == 0)
{
if (v_heqProofs_4331_ == 0)
{
if (v_heqProofs_4333_ == 0)
{
v___y_4227_ = v_a_4321_;
v_ctor_4228_ = v_ctor_4330_;
v___y_4229_ = v___x_4058_;
v___y_4230_ = v___y_4312_;
v___y_4231_ = v___y_4315_;
v___y_4232_ = v___y_4309_;
v___y_4233_ = v___y_4314_;
v___y_4234_ = v___y_4313_;
v___y_4235_ = v___y_4311_;
v___y_4236_ = v___y_4317_;
v___y_4237_ = v___y_4310_;
v___y_4238_ = v___y_4318_;
v___y_4239_ = v___x_4063_;
v___y_4240_ = v_a_4327_;
v___y_4241_ = v___y_4316_;
goto v___jp_4226_;
}
else
{
lean_inc_ref(v_self_4332_);
lean_inc_ref(v_self_4329_);
v___y_4282_ = v_a_4321_;
v___y_4283_ = v___y_4316_;
v___y_4284_ = v___y_4317_;
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4335_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4314_;
v___y_4290_ = v___y_4318_;
v___y_4291_ = v_self_4329_;
v___y_4292_ = v_self_4332_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v_a_4327_;
v___y_4295_ = v___y_4309_;
v___y_4296_ = v___y_4313_;
goto v___jp_4281_;
}
}
else
{
lean_inc_ref(v_self_4332_);
lean_inc_ref(v_self_4329_);
v___y_4282_ = v_a_4321_;
v___y_4283_ = v___y_4316_;
v___y_4284_ = v___y_4317_;
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4335_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4314_;
v___y_4290_ = v___y_4318_;
v___y_4291_ = v_self_4329_;
v___y_4292_ = v_self_4332_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v_a_4327_;
v___y_4295_ = v___y_4309_;
v___y_4296_ = v___y_4313_;
goto v___jp_4281_;
}
}
else
{
lean_inc_ref(v_self_4332_);
lean_inc_ref(v_self_4329_);
v___y_4282_ = v_a_4321_;
v___y_4283_ = v___y_4316_;
v___y_4284_ = v___y_4317_;
v___y_4285_ = v___y_4312_;
v___y_4286_ = v___y_4315_;
v___y_4287_ = v___x_4335_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4314_;
v___y_4290_ = v___y_4318_;
v___y_4291_ = v_self_4329_;
v___y_4292_ = v_self_4332_;
v___y_4293_ = v___y_4310_;
v___y_4294_ = v_a_4327_;
v___y_4295_ = v___y_4309_;
v___y_4296_ = v___y_4313_;
goto v___jp_4281_;
}
}
else
{
v___y_4268_ = v___y_4316_;
v___y_4269_ = v_a_4321_;
v___y_4270_ = v___y_4317_;
v___y_4271_ = v___y_4312_;
v___y_4272_ = v___y_4315_;
v___y_4273_ = v___y_4311_;
v___y_4274_ = v___y_4314_;
v___y_4275_ = v___y_4318_;
v___y_4276_ = v___y_4310_;
v___y_4277_ = v___y_4309_;
v___y_4278_ = v_a_4327_;
v___y_4279_ = v___y_4313_;
goto v___jp_4267_;
}
}
else
{
v___y_4268_ = v___y_4316_;
v___y_4269_ = v_a_4321_;
v___y_4270_ = v___y_4317_;
v___y_4271_ = v___y_4312_;
v___y_4272_ = v___y_4315_;
v___y_4273_ = v___y_4311_;
v___y_4274_ = v___y_4314_;
v___y_4275_ = v___y_4318_;
v___y_4276_ = v___y_4310_;
v___y_4277_ = v___y_4309_;
v___y_4278_ = v_a_4327_;
v___y_4279_ = v___y_4313_;
goto v___jp_4267_;
}
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4321_);
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4336_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4323_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4323_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4344_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4320_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4320_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
else
{
lean_object* v_toCold_4390_; lean_object* v_options_4391_; uint8_t v_hasTrace_4392_; 
lean_dec(v_a_4053_);
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
v_toCold_4390_ = lean_ctor_get(v_a_4042_, 0);
v_options_4391_ = lean_ctor_get(v_toCold_4390_, 2);
v_hasTrace_4392_ = lean_ctor_get_uint8(v_options_4391_, sizeof(void*)*1);
if (v_hasTrace_4392_ == 0)
{
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
goto v___jp_4045_;
}
else
{
lean_object* v_inheritedTraceOptions_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; 
v_inheritedTraceOptions_4393_ = lean_ctor_get(v_toCold_4390_, 11);
v___x_4394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4393_, v_options_4391_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
goto v___jp_4045_;
}
else
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Meta_Grind_updateLastTag(v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v___x_4398_; 
lean_dec_ref_known(v___x_4397_, 1);
v___x_4398_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4030_, v_a_4034_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4031_, v_a_4034_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_a_4401_);
lean_dec_ref_known(v___x_4400_, 1);
v___x_4402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v_a_4399_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v_a_4401_);
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4394_, v___x_4406_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_dec_ref_known(v___x_4407_, 1);
goto v___jp_4045_;
}
else
{
return v___x_4407_;
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4399_);
v_a_4408_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4400_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4400_);
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
lean_dec_ref(v_rhs_4031_);
v_a_4416_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4398_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4398_);
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
}
else
{
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
return v___x_4397_;
}
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_a_4050_);
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4424_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4052_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4052_);
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
lean_dec_ref(v_proof_4032_);
lean_dec_ref(v_rhs_4031_);
lean_dec_ref(v_lhs_4030_);
v_a_4432_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4049_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4049_);
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
v___jp_4045_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = lean_box(0);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4440_, lean_object* v_rhs_4441_, lean_object* v_proof_4442_, lean_object* v_isHEq_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
uint8_t v_isHEq_boxed_4455_; lean_object* v_res_4456_; 
v_isHEq_boxed_4455_ = lean_unbox(v_isHEq_4443_);
v_res_4456_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4440_, v_rhs_4441_, v_proof_4442_, v_isHEq_boxed_4455_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec(v_a_4444_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4459_){
_start:
{
lean_object* v___x_4461_; lean_object* v_toGoalState_4462_; lean_object* v_mvarId_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4499_; 
v___x_4461_ = lean_st_ref_take(v_a_4459_);
v_toGoalState_4462_ = lean_ctor_get(v___x_4461_, 0);
v_mvarId_4463_ = lean_ctor_get(v___x_4461_, 1);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4465_ = v___x_4461_;
v_isShared_4466_ = v_isSharedCheck_4499_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_mvarId_4463_);
lean_inc(v_toGoalState_4462_);
lean_dec(v___x_4461_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4499_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v_nextDeclIdx_4467_; lean_object* v_enodeMap_4468_; lean_object* v_exprs_4469_; lean_object* v_parents_4470_; lean_object* v_congrTable_4471_; lean_object* v_appMap_4472_; lean_object* v_indicesFound_4473_; uint8_t v_inconsistent_4474_; lean_object* v_nextIdx_4475_; lean_object* v_newRawFacts_4476_; lean_object* v_facts_4477_; lean_object* v_extThms_4478_; lean_object* v_ematch_4479_; lean_object* v_inj_4480_; lean_object* v_split_4481_; lean_object* v_clean_4482_; lean_object* v_sstates_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4497_; 
v_nextDeclIdx_4467_ = lean_ctor_get(v_toGoalState_4462_, 0);
v_enodeMap_4468_ = lean_ctor_get(v_toGoalState_4462_, 1);
v_exprs_4469_ = lean_ctor_get(v_toGoalState_4462_, 2);
v_parents_4470_ = lean_ctor_get(v_toGoalState_4462_, 3);
v_congrTable_4471_ = lean_ctor_get(v_toGoalState_4462_, 4);
v_appMap_4472_ = lean_ctor_get(v_toGoalState_4462_, 5);
v_indicesFound_4473_ = lean_ctor_get(v_toGoalState_4462_, 6);
v_inconsistent_4474_ = lean_ctor_get_uint8(v_toGoalState_4462_, sizeof(void*)*17);
v_nextIdx_4475_ = lean_ctor_get(v_toGoalState_4462_, 8);
v_newRawFacts_4476_ = lean_ctor_get(v_toGoalState_4462_, 9);
v_facts_4477_ = lean_ctor_get(v_toGoalState_4462_, 10);
v_extThms_4478_ = lean_ctor_get(v_toGoalState_4462_, 11);
v_ematch_4479_ = lean_ctor_get(v_toGoalState_4462_, 12);
v_inj_4480_ = lean_ctor_get(v_toGoalState_4462_, 13);
v_split_4481_ = lean_ctor_get(v_toGoalState_4462_, 14);
v_clean_4482_ = lean_ctor_get(v_toGoalState_4462_, 15);
v_sstates_4483_ = lean_ctor_get(v_toGoalState_4462_, 16);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_toGoalState_4462_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; 
v_unused_4498_ = lean_ctor_get(v_toGoalState_4462_, 7);
lean_dec(v_unused_4498_);
v___x_4485_ = v_toGoalState_4462_;
v_isShared_4486_ = v_isSharedCheck_4497_;
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
lean_inc(v_indicesFound_4473_);
lean_inc(v_appMap_4472_);
lean_inc(v_congrTable_4471_);
lean_inc(v_parents_4470_);
lean_inc(v_exprs_4469_);
lean_inc(v_enodeMap_4468_);
lean_inc(v_nextDeclIdx_4467_);
lean_dec(v_toGoalState_4462_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4497_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 7, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_nextDeclIdx_4467_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_enodeMap_4468_);
lean_ctor_set(v_reuseFailAlloc_4496_, 2, v_exprs_4469_);
lean_ctor_set(v_reuseFailAlloc_4496_, 3, v_parents_4470_);
lean_ctor_set(v_reuseFailAlloc_4496_, 4, v_congrTable_4471_);
lean_ctor_set(v_reuseFailAlloc_4496_, 5, v_appMap_4472_);
lean_ctor_set(v_reuseFailAlloc_4496_, 6, v_indicesFound_4473_);
lean_ctor_set(v_reuseFailAlloc_4496_, 7, v___x_4487_);
lean_ctor_set(v_reuseFailAlloc_4496_, 8, v_nextIdx_4475_);
lean_ctor_set(v_reuseFailAlloc_4496_, 9, v_newRawFacts_4476_);
lean_ctor_set(v_reuseFailAlloc_4496_, 10, v_facts_4477_);
lean_ctor_set(v_reuseFailAlloc_4496_, 11, v_extThms_4478_);
lean_ctor_set(v_reuseFailAlloc_4496_, 12, v_ematch_4479_);
lean_ctor_set(v_reuseFailAlloc_4496_, 13, v_inj_4480_);
lean_ctor_set(v_reuseFailAlloc_4496_, 14, v_split_4481_);
lean_ctor_set(v_reuseFailAlloc_4496_, 15, v_clean_4482_);
lean_ctor_set(v_reuseFailAlloc_4496_, 16, v_sstates_4483_);
lean_ctor_set_uint8(v_reuseFailAlloc_4496_, sizeof(void*)*17, v_inconsistent_4474_);
v___x_4489_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4491_; 
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4489_);
v___x_4491_ = v___x_4465_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_mvarId_4463_);
v___x_4491_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = lean_st_ref_put(v_a_4459_, v___x_4491_);
v___x_4493_ = lean_box(0);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
return v___x_4494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4500_);
lean_dec(v_a_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4503_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4527_){
_start:
{
lean_object* v___x_4529_; lean_object* v_toGoalState_4530_; lean_object* v_newFacts_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4529_ = lean_st_ref_get(v_a_4527_);
v_toGoalState_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc_ref(v_toGoalState_4530_);
lean_dec(v___x_4529_);
v_newFacts_4531_ = lean_ctor_get(v_toGoalState_4530_, 7);
lean_inc_ref(v_newFacts_4531_);
lean_dec_ref(v_toGoalState_4530_);
v___x_4532_ = lean_array_get_size(v_newFacts_4531_);
v___x_4533_ = lean_unsigned_to_nat(1u);
v___x_4534_ = lean_nat_sub(v___x_4532_, v___x_4533_);
v___x_4535_ = lean_nat_dec_lt(v___x_4534_, v___x_4532_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec(v___x_4534_);
lean_dec_ref(v_newFacts_4531_);
v___x_4536_ = lean_box(0);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; lean_object* v_toGoalState_4539_; lean_object* v_mvarId_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4577_; 
v___x_4538_ = lean_st_ref_take(v_a_4527_);
v_toGoalState_4539_ = lean_ctor_get(v___x_4538_, 0);
v_mvarId_4540_ = lean_ctor_get(v___x_4538_, 1);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4542_ = v___x_4538_;
v_isShared_4543_ = v_isSharedCheck_4577_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_mvarId_4540_);
lean_inc(v_toGoalState_4539_);
lean_dec(v___x_4538_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4577_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v_nextDeclIdx_4544_; lean_object* v_enodeMap_4545_; lean_object* v_exprs_4546_; lean_object* v_parents_4547_; lean_object* v_congrTable_4548_; lean_object* v_appMap_4549_; lean_object* v_indicesFound_4550_; lean_object* v_newFacts_4551_; uint8_t v_inconsistent_4552_; lean_object* v_nextIdx_4553_; lean_object* v_newRawFacts_4554_; lean_object* v_facts_4555_; lean_object* v_extThms_4556_; lean_object* v_ematch_4557_; lean_object* v_inj_4558_; lean_object* v_split_4559_; lean_object* v_clean_4560_; lean_object* v_sstates_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4576_; 
v_nextDeclIdx_4544_ = lean_ctor_get(v_toGoalState_4539_, 0);
v_enodeMap_4545_ = lean_ctor_get(v_toGoalState_4539_, 1);
v_exprs_4546_ = lean_ctor_get(v_toGoalState_4539_, 2);
v_parents_4547_ = lean_ctor_get(v_toGoalState_4539_, 3);
v_congrTable_4548_ = lean_ctor_get(v_toGoalState_4539_, 4);
v_appMap_4549_ = lean_ctor_get(v_toGoalState_4539_, 5);
v_indicesFound_4550_ = lean_ctor_get(v_toGoalState_4539_, 6);
v_newFacts_4551_ = lean_ctor_get(v_toGoalState_4539_, 7);
v_inconsistent_4552_ = lean_ctor_get_uint8(v_toGoalState_4539_, sizeof(void*)*17);
v_nextIdx_4553_ = lean_ctor_get(v_toGoalState_4539_, 8);
v_newRawFacts_4554_ = lean_ctor_get(v_toGoalState_4539_, 9);
v_facts_4555_ = lean_ctor_get(v_toGoalState_4539_, 10);
v_extThms_4556_ = lean_ctor_get(v_toGoalState_4539_, 11);
v_ematch_4557_ = lean_ctor_get(v_toGoalState_4539_, 12);
v_inj_4558_ = lean_ctor_get(v_toGoalState_4539_, 13);
v_split_4559_ = lean_ctor_get(v_toGoalState_4539_, 14);
v_clean_4560_ = lean_ctor_get(v_toGoalState_4539_, 15);
v_sstates_4561_ = lean_ctor_get(v_toGoalState_4539_, 16);
v_isSharedCheck_4576_ = !lean_is_exclusive(v_toGoalState_4539_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4563_ = v_toGoalState_4539_;
v_isShared_4564_ = v_isSharedCheck_4576_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_sstates_4561_);
lean_inc(v_clean_4560_);
lean_inc(v_split_4559_);
lean_inc(v_inj_4558_);
lean_inc(v_ematch_4557_);
lean_inc(v_extThms_4556_);
lean_inc(v_facts_4555_);
lean_inc(v_newRawFacts_4554_);
lean_inc(v_nextIdx_4553_);
lean_inc(v_newFacts_4551_);
lean_inc(v_indicesFound_4550_);
lean_inc(v_appMap_4549_);
lean_inc(v_congrTable_4548_);
lean_inc(v_parents_4547_);
lean_inc(v_exprs_4546_);
lean_inc(v_enodeMap_4545_);
lean_inc(v_nextDeclIdx_4544_);
lean_dec(v_toGoalState_4539_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4576_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = lean_array_pop(v_newFacts_4551_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 7, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_nextDeclIdx_4544_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_enodeMap_4545_);
lean_ctor_set(v_reuseFailAlloc_4575_, 2, v_exprs_4546_);
lean_ctor_set(v_reuseFailAlloc_4575_, 3, v_parents_4547_);
lean_ctor_set(v_reuseFailAlloc_4575_, 4, v_congrTable_4548_);
lean_ctor_set(v_reuseFailAlloc_4575_, 5, v_appMap_4549_);
lean_ctor_set(v_reuseFailAlloc_4575_, 6, v_indicesFound_4550_);
lean_ctor_set(v_reuseFailAlloc_4575_, 7, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4575_, 8, v_nextIdx_4553_);
lean_ctor_set(v_reuseFailAlloc_4575_, 9, v_newRawFacts_4554_);
lean_ctor_set(v_reuseFailAlloc_4575_, 10, v_facts_4555_);
lean_ctor_set(v_reuseFailAlloc_4575_, 11, v_extThms_4556_);
lean_ctor_set(v_reuseFailAlloc_4575_, 12, v_ematch_4557_);
lean_ctor_set(v_reuseFailAlloc_4575_, 13, v_inj_4558_);
lean_ctor_set(v_reuseFailAlloc_4575_, 14, v_split_4559_);
lean_ctor_set(v_reuseFailAlloc_4575_, 15, v_clean_4560_);
lean_ctor_set(v_reuseFailAlloc_4575_, 16, v_sstates_4561_);
lean_ctor_set_uint8(v_reuseFailAlloc_4575_, sizeof(void*)*17, v_inconsistent_4552_);
v___x_4567_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4569_; 
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4567_);
v___x_4569_ = v___x_4542_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_mvarId_4540_);
v___x_4569_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4570_ = lean_st_ref_put(v_a_4527_, v___x_4569_);
v___x_4571_ = lean_array_fget(v_newFacts_4531_, v___x_4534_);
lean_dec(v___x_4534_);
lean_dec_ref(v_newFacts_4531_);
v___x_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4578_);
lean_dec(v_a_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4581_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec(v_a_4593_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4605_, lean_object* v_rhs_4606_, lean_object* v_proof_4607_, uint8_t v_isHEq_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4605_, v_rhs_4606_, v_proof_4607_, v_isHEq_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v___x_4621_; 
lean_dec_ref_known(v___x_4620_, 1);
lean_inc(v_a_4618_);
lean_inc_ref(v_a_4617_);
lean_inc(v_a_4616_);
lean_inc_ref(v_a_4615_);
lean_inc(v_a_4614_);
lean_inc_ref(v_a_4613_);
lean_inc(v_a_4612_);
lean_inc_ref(v_a_4611_);
lean_inc(v_a_4610_);
lean_inc(v_a_4609_);
v___x_4621_ = lean_grind_process_new_facts(v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
return v___x_4621_;
}
else
{
return v___x_4620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4622_, lean_object* v_rhs_4623_, lean_object* v_proof_4624_, lean_object* v_isHEq_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
uint8_t v_isHEq_boxed_4637_; lean_object* v_res_4638_; 
v_isHEq_boxed_4637_ = lean_unbox(v_isHEq_4625_);
v_res_4638_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4622_, v_rhs_4623_, v_proof_4624_, v_isHEq_boxed_4637_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec(v_a_4626_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4639_, lean_object* v_rhs_4640_, lean_object* v_proof_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
uint8_t v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = 0;
v___x_4654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4639_, v_rhs_4640_, v_proof_4641_, v___x_4653_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4655_, lean_object* v_rhs_4656_, lean_object* v_proof_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4655_, v_rhs_4656_, v_proof_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec(v_a_4658_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4670_, lean_object* v_rhs_4671_, lean_object* v_proof_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
uint8_t v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = 1;
v___x_4685_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4670_, v_rhs_4671_, v_proof_4672_, v___x_4684_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4686_, lean_object* v_rhs_4687_, lean_object* v_proof_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4686_, v_rhs_4687_, v_proof_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec(v_a_4689_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___x_4704_; lean_object* v_toGoalState_4705_; lean_object* v_mvarId_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4742_; 
v___x_4704_ = lean_st_ref_take(v_a_4702_);
v_toGoalState_4705_ = lean_ctor_get(v___x_4704_, 0);
v_mvarId_4706_ = lean_ctor_get(v___x_4704_, 1);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4708_ = v___x_4704_;
v_isShared_4709_ = v_isSharedCheck_4742_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_mvarId_4706_);
lean_inc(v_toGoalState_4705_);
lean_dec(v___x_4704_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4742_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_nextDeclIdx_4710_; lean_object* v_enodeMap_4711_; lean_object* v_exprs_4712_; lean_object* v_parents_4713_; lean_object* v_congrTable_4714_; lean_object* v_appMap_4715_; lean_object* v_indicesFound_4716_; lean_object* v_newFacts_4717_; uint8_t v_inconsistent_4718_; lean_object* v_nextIdx_4719_; lean_object* v_newRawFacts_4720_; lean_object* v_facts_4721_; lean_object* v_extThms_4722_; lean_object* v_ematch_4723_; lean_object* v_inj_4724_; lean_object* v_split_4725_; lean_object* v_clean_4726_; lean_object* v_sstates_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4741_; 
v_nextDeclIdx_4710_ = lean_ctor_get(v_toGoalState_4705_, 0);
v_enodeMap_4711_ = lean_ctor_get(v_toGoalState_4705_, 1);
v_exprs_4712_ = lean_ctor_get(v_toGoalState_4705_, 2);
v_parents_4713_ = lean_ctor_get(v_toGoalState_4705_, 3);
v_congrTable_4714_ = lean_ctor_get(v_toGoalState_4705_, 4);
v_appMap_4715_ = lean_ctor_get(v_toGoalState_4705_, 5);
v_indicesFound_4716_ = lean_ctor_get(v_toGoalState_4705_, 6);
v_newFacts_4717_ = lean_ctor_get(v_toGoalState_4705_, 7);
v_inconsistent_4718_ = lean_ctor_get_uint8(v_toGoalState_4705_, sizeof(void*)*17);
v_nextIdx_4719_ = lean_ctor_get(v_toGoalState_4705_, 8);
v_newRawFacts_4720_ = lean_ctor_get(v_toGoalState_4705_, 9);
v_facts_4721_ = lean_ctor_get(v_toGoalState_4705_, 10);
v_extThms_4722_ = lean_ctor_get(v_toGoalState_4705_, 11);
v_ematch_4723_ = lean_ctor_get(v_toGoalState_4705_, 12);
v_inj_4724_ = lean_ctor_get(v_toGoalState_4705_, 13);
v_split_4725_ = lean_ctor_get(v_toGoalState_4705_, 14);
v_clean_4726_ = lean_ctor_get(v_toGoalState_4705_, 15);
v_sstates_4727_ = lean_ctor_get(v_toGoalState_4705_, 16);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_toGoalState_4705_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4729_ = v_toGoalState_4705_;
v_isShared_4730_ = v_isSharedCheck_4741_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_sstates_4727_);
lean_inc(v_clean_4726_);
lean_inc(v_split_4725_);
lean_inc(v_inj_4724_);
lean_inc(v_ematch_4723_);
lean_inc(v_extThms_4722_);
lean_inc(v_facts_4721_);
lean_inc(v_newRawFacts_4720_);
lean_inc(v_nextIdx_4719_);
lean_inc(v_newFacts_4717_);
lean_inc(v_indicesFound_4716_);
lean_inc(v_appMap_4715_);
lean_inc(v_congrTable_4714_);
lean_inc(v_parents_4713_);
lean_inc(v_exprs_4712_);
lean_inc(v_enodeMap_4711_);
lean_inc(v_nextDeclIdx_4710_);
lean_dec(v_toGoalState_4705_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4741_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4731_ = l_Lean_PersistentArray_push___redArg(v_facts_4721_, v_fact_4701_);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 10, v___x_4731_);
v___x_4733_ = v___x_4729_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_nextDeclIdx_4710_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_enodeMap_4711_);
lean_ctor_set(v_reuseFailAlloc_4740_, 2, v_exprs_4712_);
lean_ctor_set(v_reuseFailAlloc_4740_, 3, v_parents_4713_);
lean_ctor_set(v_reuseFailAlloc_4740_, 4, v_congrTable_4714_);
lean_ctor_set(v_reuseFailAlloc_4740_, 5, v_appMap_4715_);
lean_ctor_set(v_reuseFailAlloc_4740_, 6, v_indicesFound_4716_);
lean_ctor_set(v_reuseFailAlloc_4740_, 7, v_newFacts_4717_);
lean_ctor_set(v_reuseFailAlloc_4740_, 8, v_nextIdx_4719_);
lean_ctor_set(v_reuseFailAlloc_4740_, 9, v_newRawFacts_4720_);
lean_ctor_set(v_reuseFailAlloc_4740_, 10, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4740_, 11, v_extThms_4722_);
lean_ctor_set(v_reuseFailAlloc_4740_, 12, v_ematch_4723_);
lean_ctor_set(v_reuseFailAlloc_4740_, 13, v_inj_4724_);
lean_ctor_set(v_reuseFailAlloc_4740_, 14, v_split_4725_);
lean_ctor_set(v_reuseFailAlloc_4740_, 15, v_clean_4726_);
lean_ctor_set(v_reuseFailAlloc_4740_, 16, v_sstates_4727_);
lean_ctor_set_uint8(v_reuseFailAlloc_4740_, sizeof(void*)*17, v_inconsistent_4718_);
v___x_4733_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4735_; 
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 0, v___x_4733_);
v___x_4735_ = v___x_4708_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v_mvarId_4706_);
v___x_4735_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = lean_st_ref_put(v_a_4702_, v___x_4735_);
v___x_4737_ = lean_box(0);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
return v___x_4738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4743_, v_a_4744_);
lean_dec(v_a_4744_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4747_, v_a_4748_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
lean_dec(v_a_4762_);
lean_dec(v_a_4761_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4773_, lean_object* v_rhs_4774_, lean_object* v_proof_4775_, lean_object* v_generation_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; 
lean_inc_ref(v_rhs_4774_);
lean_inc_ref(v_lhs_4773_);
v___x_4788_ = l_Lean_Meta_mkEq(v_lhs_4773_, v_rhs_4774_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4800_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc_n(v_a_4789_, 2);
lean_dec_ref_known(v___x_4788_, 1);
v___x_4790_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4789_, v_a_4777_);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4800_ == 0)
{
lean_object* v_unused_4801_; 
v_unused_4801_ = lean_ctor_get(v___x_4790_, 0);
lean_dec(v_unused_4801_);
v___x_4792_ = v___x_4790_;
v_isShared_4793_ = v_isSharedCheck_4800_;
goto v_resetjp_4791_;
}
else
{
lean_dec(v___x_4790_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4800_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
lean_ctor_set_tag(v___x_4792_, 1);
lean_ctor_set(v___x_4792_, 0, v_a_4789_);
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4789_);
v___x_4795_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
lean_object* v___x_4796_; 
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc_ref(v_a_4783_);
lean_inc(v_a_4782_);
lean_inc_ref(v_a_4781_);
lean_inc(v_a_4780_);
lean_inc_ref(v_a_4779_);
lean_inc(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc_ref(v___x_4795_);
lean_inc(v_generation_4776_);
lean_inc_ref(v_lhs_4773_);
v___x_4796_ = lean_grind_internalize(v_lhs_4773_, v_generation_4776_, v___x_4795_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v___x_4797_; 
lean_dec_ref_known(v___x_4796_, 1);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc_ref(v_a_4783_);
lean_inc(v_a_4782_);
lean_inc_ref(v_a_4781_);
lean_inc(v_a_4780_);
lean_inc_ref(v_a_4779_);
lean_inc(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc_ref(v_rhs_4774_);
v___x_4797_ = lean_grind_internalize(v_rhs_4774_, v_generation_4776_, v___x_4795_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v___x_4798_; 
lean_dec_ref_known(v___x_4797_, 1);
v___x_4798_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4773_, v_rhs_4774_, v_proof_4775_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
return v___x_4798_;
}
else
{
lean_dec_ref(v_proof_4775_);
lean_dec_ref(v_rhs_4774_);
lean_dec_ref(v_lhs_4773_);
return v___x_4797_;
}
}
else
{
lean_dec_ref(v___x_4795_);
lean_dec(v_generation_4776_);
lean_dec_ref(v_proof_4775_);
lean_dec_ref(v_rhs_4774_);
lean_dec_ref(v_lhs_4773_);
return v___x_4796_;
}
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec(v_generation_4776_);
lean_dec_ref(v_proof_4775_);
lean_dec_ref(v_rhs_4774_);
lean_dec_ref(v_lhs_4773_);
v_a_4802_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4788_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4788_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4810_, lean_object* v_rhs_4811_, lean_object* v_proof_4812_, lean_object* v_generation_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4810_, v_rhs_4811_, v_proof_4812_, v_generation_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec(v_a_4814_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4826_, lean_object* v_generation_4827_, lean_object* v_p_4828_, uint8_t v_isNeg_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_box(0);
lean_inc(v_a_4839_);
lean_inc_ref(v_a_4838_);
lean_inc(v_a_4837_);
lean_inc_ref(v_a_4836_);
lean_inc(v_a_4835_);
lean_inc_ref(v_a_4834_);
lean_inc(v_a_4833_);
lean_inc_ref(v_a_4832_);
lean_inc(v_a_4831_);
lean_inc(v_a_4830_);
lean_inc_ref(v_p_4828_);
v___x_4842_ = lean_grind_internalize(v_p_4828_, v_generation_4827_, v___x_4841_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_dec_ref_known(v___x_4842_, 1);
if (v_isNeg_4829_ == 0)
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4834_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___x_4843_, 1);
v___x_4845_ = l_Lean_Meta_mkEqTrue(v_proof_4826_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4847_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
lean_inc(v_a_4846_);
lean_dec_ref_known(v___x_4845_, 1);
v___x_4847_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4828_, v_a_4844_, v_a_4846_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
return v___x_4847_;
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_dec(v_a_4844_);
lean_dec_ref(v_p_4828_);
v_a_4848_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4845_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4845_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec_ref(v_p_4828_);
lean_dec_ref(v_proof_4826_);
v_a_4856_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4843_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4843_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4834_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_Meta_mkEqFalse(v_proof_4826_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v___x_4868_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4828_, v_a_4865_, v_a_4867_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
return v___x_4868_;
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v_a_4865_);
lean_dec_ref(v_p_4828_);
v_a_4869_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4866_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4866_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec_ref(v_p_4828_);
lean_dec_ref(v_proof_4826_);
v_a_4877_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4864_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4864_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4828_);
lean_dec_ref(v_proof_4826_);
return v___x_4842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4885_, lean_object* v_generation_4886_, lean_object* v_p_4887_, lean_object* v_isNeg_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
uint8_t v_isNeg_boxed_4900_; lean_object* v_res_4901_; 
v_isNeg_boxed_4900_ = lean_unbox(v_isNeg_4888_);
v_res_4901_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4885_, v_generation_4886_, v_p_4887_, v_isNeg_boxed_4900_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
lean_dec(v_a_4896_);
lean_dec_ref(v_a_4895_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
lean_dec(v_a_4890_);
lean_dec(v_a_4889_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4902_, lean_object* v_generation_4903_, lean_object* v_p_4904_, lean_object* v_lhs_4905_, lean_object* v_rhs_4906_, uint8_t v_isNeg_4907_, uint8_t v_isHEq_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
if (v_isNeg_4907_ == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_inc_ref(v_p_4904_);
v___x_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4920_, 0, v_p_4904_);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc_ref(v_a_4915_);
lean_inc(v_a_4914_);
lean_inc_ref(v_a_4913_);
lean_inc(v_a_4912_);
lean_inc_ref(v_a_4911_);
lean_inc(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v___x_4920_);
lean_inc(v_generation_4903_);
lean_inc_ref(v_lhs_4905_);
v___x_4921_ = lean_grind_internalize(v_lhs_4905_, v_generation_4903_, v___x_4920_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4921_, 1);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc_ref(v_a_4915_);
lean_inc(v_a_4914_);
lean_inc_ref(v_a_4913_);
lean_inc(v_a_4912_);
lean_inc_ref(v_a_4911_);
lean_inc(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v_rhs_4906_);
v___x_4922_ = lean_grind_internalize(v_rhs_4906_, v_generation_4903_, v___x_4920_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v___x_4923_; lean_object* v___x_4924_; 
lean_dec_ref_known(v___x_4922_, 1);
v___x_4923_ = lean_box(0);
v___x_4924_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4904_, v___x_4923_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v___x_4925_; 
lean_dec_ref_known(v___x_4924_, 1);
v___x_4925_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4905_, v_rhs_4906_, v_proof_4902_, v_isHEq_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
return v___x_4925_;
}
else
{
lean_dec_ref(v_rhs_4906_);
lean_dec_ref(v_lhs_4905_);
lean_dec_ref(v_proof_4902_);
return v___x_4924_;
}
}
else
{
lean_dec_ref(v_rhs_4906_);
lean_dec_ref(v_lhs_4905_);
lean_dec_ref(v_p_4904_);
lean_dec_ref(v_proof_4902_);
return v___x_4922_;
}
}
else
{
lean_dec_ref_known(v___x_4920_, 1);
lean_dec_ref(v_rhs_4906_);
lean_dec_ref(v_lhs_4905_);
lean_dec_ref(v_p_4904_);
lean_dec(v_generation_4903_);
lean_dec_ref(v_proof_4902_);
return v___x_4921_;
}
}
else
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec_ref(v_rhs_4906_);
lean_dec_ref(v_lhs_4905_);
v___x_4926_ = lean_box(0);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc_ref(v_a_4915_);
lean_inc(v_a_4914_);
lean_inc_ref(v_a_4913_);
lean_inc(v_a_4912_);
lean_inc_ref(v_a_4911_);
lean_inc(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v_p_4904_);
v___x_4927_ = lean_grind_internalize(v_p_4904_, v_generation_4903_, v___x_4926_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref_known(v___x_4927_, 1);
v___x_4928_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4913_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = l_Lean_Meta_mkEqFalse(v_proof_4902_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4904_, v_a_4929_, v_a_4931_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_);
return v___x_4932_;
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec(v_a_4929_);
lean_dec_ref(v_p_4904_);
v_a_4933_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4930_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4930_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec_ref(v_p_4904_);
lean_dec_ref(v_proof_4902_);
v_a_4941_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4928_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4928_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_dec_ref(v_p_4904_);
lean_dec_ref(v_proof_4902_);
return v___x_4927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4949_ = _args[0];
lean_object* v_generation_4950_ = _args[1];
lean_object* v_p_4951_ = _args[2];
lean_object* v_lhs_4952_ = _args[3];
lean_object* v_rhs_4953_ = _args[4];
lean_object* v_isNeg_4954_ = _args[5];
lean_object* v_isHEq_4955_ = _args[6];
lean_object* v_a_4956_ = _args[7];
lean_object* v_a_4957_ = _args[8];
lean_object* v_a_4958_ = _args[9];
lean_object* v_a_4959_ = _args[10];
lean_object* v_a_4960_ = _args[11];
lean_object* v_a_4961_ = _args[12];
lean_object* v_a_4962_ = _args[13];
lean_object* v_a_4963_ = _args[14];
lean_object* v_a_4964_ = _args[15];
lean_object* v_a_4965_ = _args[16];
lean_object* v_a_4966_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4967_; uint8_t v_isHEq_boxed_4968_; lean_object* v_res_4969_; 
v_isNeg_boxed_4967_ = lean_unbox(v_isNeg_4954_);
v_isHEq_boxed_4968_ = lean_unbox(v_isHEq_4955_);
v_res_4969_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4949_, v_generation_4950_, v_p_4951_, v_lhs_4952_, v_rhs_4953_, v_isNeg_boxed_4967_, v_isHEq_boxed_4968_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec(v_a_4959_);
lean_dec_ref(v_a_4958_);
lean_dec(v_a_4957_);
lean_dec(v_a_4956_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4973_, lean_object* v_generation_4974_, lean_object* v_p_4975_, uint8_t v_isNeg_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v___x_4988_; 
lean_inc_ref(v_p_4975_);
v___x_4988_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4975_, v_a_4984_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4990_ = l_Lean_Expr_cleanupAnnotations(v_a_4989_);
v___x_4991_ = l_Lean_Expr_isApp(v___x_4990_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4992_; 
lean_dec_ref(v___x_4990_);
v___x_4992_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_4992_;
}
else
{
lean_object* v_arg_4993_; lean_object* v___x_4994_; uint8_t v___x_4995_; 
v_arg_4993_ = lean_ctor_get(v___x_4990_, 1);
lean_inc_ref(v_arg_4993_);
v___x_4994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4990_);
v___x_4995_ = l_Lean_Expr_isApp(v___x_4994_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; 
lean_dec_ref(v___x_4994_);
lean_dec_ref(v_arg_4993_);
v___x_4996_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_4996_;
}
else
{
lean_object* v_arg_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; 
v_arg_4997_ = lean_ctor_get(v___x_4994_, 1);
lean_inc_ref(v_arg_4997_);
v___x_4998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4994_);
v___x_4999_ = l_Lean_Expr_isApp(v___x_4998_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref(v___x_4998_);
lean_dec_ref(v_arg_4997_);
lean_dec_ref(v_arg_4993_);
v___x_5000_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5000_;
}
else
{
lean_object* v_arg_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; uint8_t v___x_5004_; 
v_arg_5001_ = lean_ctor_get(v___x_4998_, 1);
lean_inc_ref(v_arg_5001_);
v___x_5002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4998_);
v___x_5003_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5004_ = l_Lean_Expr_isConstOf(v___x_5002_, v___x_5003_);
if (v___x_5004_ == 0)
{
uint8_t v___x_5005_; 
lean_dec_ref(v_arg_4997_);
v___x_5005_ = l_Lean_Expr_isApp(v___x_5002_);
if (v___x_5005_ == 0)
{
lean_object* v___x_5006_; 
lean_dec_ref(v___x_5002_);
lean_dec_ref(v_arg_5001_);
lean_dec_ref(v_arg_4993_);
v___x_5006_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5006_;
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5007_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5002_);
v___x_5008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5009_ = l_Lean_Expr_isConstOf(v___x_5007_, v___x_5008_);
lean_dec_ref(v___x_5007_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_dec_ref(v_arg_5001_);
lean_dec_ref(v_arg_4993_);
v___x_5010_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; 
v___x_5011_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4973_, v_generation_4974_, v_p_4975_, v_arg_5001_, v_arg_4993_, v_isNeg_4976_, v___x_5009_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5011_;
}
}
}
else
{
uint8_t v___x_5012_; 
lean_dec_ref(v___x_5002_);
v___x_5012_ = l_Lean_Expr_isProp(v_arg_5001_);
lean_dec_ref(v_arg_5001_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
v___x_5013_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4973_, v_generation_4974_, v_p_4975_, v_arg_4997_, v_arg_4993_, v_isNeg_4976_, v___x_5012_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5013_;
}
else
{
lean_object* v___x_5014_; 
lean_dec_ref(v_arg_4997_);
lean_dec_ref(v_arg_4993_);
v___x_5014_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4973_, v_generation_4974_, v_p_4975_, v_isNeg_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_5014_;
}
}
}
}
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v_p_4975_);
lean_dec(v_generation_4974_);
lean_dec_ref(v_proof_4973_);
v_a_5015_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_4988_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_4988_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5023_, lean_object* v_generation_5024_, lean_object* v_p_5025_, lean_object* v_isNeg_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
uint8_t v_isNeg_boxed_5038_; lean_object* v_res_5039_; 
v_isNeg_boxed_5038_ = lean_unbox(v_isNeg_5026_);
v_res_5039_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5023_, v_generation_5024_, v_p_5025_, v_isNeg_boxed_5038_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
lean_dec_ref(v_a_5033_);
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec(v_a_5027_);
return v_res_5039_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5048_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5049_ = l_Lean_Name_append(v___x_5048_, v___x_5047_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5050_, lean_object* v_proof_5051_, lean_object* v_generation_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___x_5095_; lean_object* v_toCold_5096_; lean_object* v_options_5097_; uint8_t v_hasTrace_5098_; 
lean_inc_ref(v_fact_5050_);
v___x_5095_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5050_, v_a_5053_);
lean_dec_ref(v___x_5095_);
v_toCold_5096_ = lean_ctor_get(v_a_5061_, 0);
v_options_5097_ = lean_ctor_get(v_toCold_5096_, 2);
v_hasTrace_5098_ = lean_ctor_get_uint8(v_options_5097_, sizeof(void*)*1);
if (v_hasTrace_5098_ == 0)
{
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
goto v___jp_5077_;
}
else
{
lean_object* v_inheritedTraceOptions_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v_inheritedTraceOptions_5099_ = lean_ctor_get(v_toCold_5096_, 11);
v___x_5100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5101_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5102_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5099_, v_options_5097_, v___x_5101_);
if (v___x_5102_ == 0)
{
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
goto v___jp_5077_;
}
else
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Meta_Grind_updateLastTag(v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
lean_dec_ref_known(v___x_5103_, 1);
lean_inc_ref(v_fact_5050_);
v___x_5104_ = l_Lean_MessageData_ofExpr(v_fact_5050_);
v___x_5105_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5100_, v___x_5104_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_dec_ref_known(v___x_5105_, 1);
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
goto v___jp_5077_;
}
else
{
lean_dec(v_generation_5052_);
lean_dec_ref(v_proof_5051_);
lean_dec_ref(v_fact_5050_);
return v___x_5105_;
}
}
else
{
lean_dec(v_generation_5052_);
lean_dec_ref(v_proof_5051_);
lean_dec_ref(v_fact_5050_);
return v___x_5103_;
}
}
}
v___jp_5064_:
{
uint8_t v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = 0;
v___x_5076_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5051_, v_generation_5052_, v_fact_5050_, v___x_5075_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
return v___x_5076_;
}
v___jp_5077_:
{
lean_object* v___x_5088_; uint8_t v___x_5089_; 
lean_inc_ref(v_fact_5050_);
v___x_5088_ = l_Lean_Expr_cleanupAnnotations(v_fact_5050_);
v___x_5089_ = l_Lean_Expr_isApp(v___x_5088_);
if (v___x_5089_ == 0)
{
lean_dec_ref(v___x_5088_);
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
goto v___jp_5064_;
}
else
{
lean_object* v_arg_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
v_arg_5090_ = lean_ctor_get(v___x_5088_, 1);
lean_inc_ref(v_arg_5090_);
v___x_5091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5088_);
v___x_5092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5093_ = l_Lean_Expr_isConstOf(v___x_5091_, v___x_5092_);
lean_dec_ref(v___x_5091_);
if (v___x_5093_ == 0)
{
lean_dec_ref(v_arg_5090_);
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
goto v___jp_5064_;
}
else
{
lean_object* v___x_5094_; 
lean_dec_ref(v_fact_5050_);
v___x_5094_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5051_, v_generation_5052_, v_arg_5090_, v___x_5093_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5106_, lean_object* v_proof_5107_, lean_object* v_generation_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5106_, v_proof_5107_, v_generation_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
lean_dec(v_a_5114_);
lean_dec_ref(v_a_5113_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5111_);
lean_dec(v_a_5110_);
lean_dec(v_a_5109_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5124_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_a_5136_; uint8_t v___x_5137_; 
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5135_, 1);
v___x_5137_ = lean_unbox(v_a_5136_);
lean_dec(v_a_5136_);
if (v___x_5137_ == 0)
{
lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5138_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5139_ = l_Lean_Core_checkSystem(v___x_5138_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v___x_5140_; 
lean_dec_ref_known(v___x_5139_, 1);
v___x_5140_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5124_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5177_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5143_ = v___x_5140_;
v_isShared_5144_ = v_isSharedCheck_5177_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5140_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5177_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
if (lean_obj_tag(v_a_5141_) == 1)
{
lean_object* v_val_5145_; 
lean_del_object(v___x_5143_);
v_val_5145_ = lean_ctor_get(v_a_5141_, 0);
lean_inc(v_val_5145_);
lean_dec_ref_known(v_a_5141_, 1);
if (lean_obj_tag(v_val_5145_) == 0)
{
lean_object* v_lhs_5146_; lean_object* v_rhs_5147_; lean_object* v_proof_5148_; uint8_t v_isHEq_5149_; lean_object* v___x_5150_; 
v_lhs_5146_ = lean_ctor_get(v_val_5145_, 0);
lean_inc_ref(v_lhs_5146_);
v_rhs_5147_ = lean_ctor_get(v_val_5145_, 1);
lean_inc_ref(v_rhs_5147_);
v_proof_5148_ = lean_ctor_get(v_val_5145_, 2);
lean_inc_ref(v_proof_5148_);
v_isHEq_5149_ = lean_ctor_get_uint8(v_val_5145_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5145_, 3);
v___x_5150_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5146_, v_rhs_5147_, v_proof_5148_, v_isHEq_5149_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_dec_ref_known(v___x_5150_, 1);
goto _start;
}
else
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5159_; 
v_a_5152_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5154_ = v___x_5150_;
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5150_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5157_; 
if (v_isShared_5155_ == 0)
{
v___x_5157_ = v___x_5154_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
}
else
{
lean_object* v_prop_5160_; lean_object* v_proof_5161_; lean_object* v_generation_5162_; lean_object* v___x_5163_; 
v_prop_5160_ = lean_ctor_get(v_val_5145_, 0);
lean_inc_ref(v_prop_5160_);
v_proof_5161_ = lean_ctor_get(v_val_5145_, 1);
lean_inc_ref(v_proof_5161_);
v_generation_5162_ = lean_ctor_get(v_val_5145_, 2);
lean_inc(v_generation_5162_);
lean_dec_ref_known(v_val_5145_, 3);
v___x_5163_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5160_, v_proof_5161_, v_generation_5162_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_dec_ref_known(v___x_5163_, 1);
goto _start;
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
v_a_5165_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5163_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5163_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
}
else
{
lean_object* v___x_5173_; lean_object* v___x_5175_; 
lean_dec(v_a_5141_);
v___x_5173_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5173_);
v___x_5175_ = v___x_5143_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5173_);
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
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
v_a_5178_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5140_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5140_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
v_a_5186_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5139_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5139_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
else
{
lean_object* v___x_5194_; 
v___x_5194_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5124_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5202_; 
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5202_ == 0)
{
lean_object* v_unused_5203_; 
v_unused_5203_ = lean_ctor_get(v___x_5194_, 0);
lean_dec(v_unused_5203_);
v___x_5196_ = v___x_5194_;
v_isShared_5197_ = v_isSharedCheck_5202_;
goto v_resetjp_5195_;
}
else
{
lean_dec(v___x_5194_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5202_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v___x_5198_);
v___x_5200_ = v___x_5196_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
else
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5211_; 
v_a_5204_ = lean_ctor_get(v___x_5194_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5211_ == 0)
{
v___x_5206_ = v___x_5194_;
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5194_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5211_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5209_; 
if (v_isShared_5207_ == 0)
{
v___x_5209_ = v___x_5206_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5204_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
v_a_5212_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5135_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5135_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
lean_dec(v___y_5221_);
lean_dec(v___y_5220_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_);
lean_dec(v_a_5241_);
lean_dec_ref(v_a_5240_);
lean_dec(v_a_5239_);
lean_dec_ref(v_a_5238_);
lean_dec(v_a_5237_);
lean_dec_ref(v_a_5236_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
lean_dec(v_a_5232_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5257_; 
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5246_ = v___x_5243_;
v_isShared_5247_ = v_isSharedCheck_5257_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5243_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5257_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v_fst_5248_; 
v_fst_5248_ = lean_ctor_get(v_a_5244_, 0);
lean_inc(v_fst_5248_);
lean_dec(v_a_5244_);
if (lean_obj_tag(v_fst_5248_) == 0)
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = lean_box(0);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5249_);
v___x_5251_ = v___x_5246_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
else
{
lean_object* v_val_5253_; lean_object* v___x_5255_; 
v_val_5253_ = lean_ctor_get(v_fst_5248_, 0);
lean_inc(v_val_5253_);
lean_dec_ref_known(v_fst_5248_, 1);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v_val_5253_);
v___x_5255_ = v___x_5246_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_val_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
v_a_5258_ = lean_ctor_get(v___x_5243_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5243_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5243_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = lean_grind_process_new_facts(v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5278_, lean_object* v_a_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v___x_5291_; 
v___x_5291_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
return v___x_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5292_, lean_object* v_a_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5292_, v_a_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
lean_dec(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec_ref(v_a_5293_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5306_, lean_object* v_proof_5307_, lean_object* v_generation_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_){
_start:
{
uint8_t v___x_5320_; 
lean_inc_ref(v_fact_5306_);
v___x_5320_ = l_Lean_Expr_isTrue(v_fact_5306_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5309_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5333_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5333_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5333_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
uint8_t v___x_5326_; 
v___x_5326_ = lean_unbox(v_a_5322_);
lean_dec(v_a_5322_);
if (v___x_5326_ == 0)
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_del_object(v___x_5324_);
v___x_5327_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5309_);
lean_dec_ref(v___x_5327_);
v___x_5328_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5306_, v_proof_5307_, v_generation_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_);
return v___x_5328_;
}
else
{
lean_object* v___x_5329_; lean_object* v___x_5331_; 
lean_dec(v_generation_5308_);
lean_dec_ref(v_proof_5307_);
lean_dec_ref(v_fact_5306_);
v___x_5329_ = lean_box(0);
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v___x_5329_);
v___x_5331_ = v___x_5324_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5329_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
lean_dec(v_generation_5308_);
lean_dec_ref(v_proof_5307_);
lean_dec_ref(v_fact_5306_);
v_a_5334_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5321_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5321_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
lean_dec(v_generation_5308_);
lean_dec_ref(v_proof_5307_);
lean_dec_ref(v_fact_5306_);
v___x_5342_ = lean_box(0);
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
return v___x_5343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5344_, lean_object* v_proof_5345_, lean_object* v_generation_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_Meta_Grind_add(v_fact_5344_, v_proof_5345_, v_generation_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec(v_a_5347_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5359_, lean_object* v_generation_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v___x_5372_; 
lean_inc(v_fvarId_5359_);
v___x_5372_ = l_Lean_FVarId_getType___redArg(v_fvarId_5359_, v_a_5367_, v_a_5369_, v_a_5370_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5372_, 1);
v___x_5374_ = l_Lean_mkFVar(v_fvarId_5359_);
v___x_5375_ = l_Lean_Meta_Grind_add(v_a_5373_, v___x_5374_, v_generation_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_);
return v___x_5375_;
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec(v_generation_5360_);
lean_dec(v_fvarId_5359_);
v_a_5376_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5372_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5372_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5384_, lean_object* v_generation_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5384_, v_generation_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec_ref(v_a_5392_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec(v_a_5386_);
return v_res_5397_;
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
