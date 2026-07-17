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
size_t v_x_28263__boxed_351_; lean_object* v_res_352_; 
v_x_28263__boxed_351_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_res_352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_347_, v_x_348_, v_x_28263__boxed_351_, v_x_350_);
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
size_t v_x_28725__boxed_603_; lean_object* v_res_604_; 
v_x_28725__boxed_603_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_604_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_598_, v_00_u03b2_599_, v_x_600_, v_x_28725__boxed_603_, v_x_602_);
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
size_t v_x_10247__boxed_783_; uint8_t v_res_784_; lean_object* v_r_785_; 
v_x_10247__boxed_783_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_784_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_780_, v_x_10247__boxed_783_, v_x_782_);
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
size_t v_x_10530__boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v_x_10530__boxed_951_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_952_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_947_, v_x_948_, v_x_10530__boxed_951_, v_x_950_);
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
lean_dec_ref(v_fn_1249_);
lean_dec_ref_known(v_snd_1221_, 2);
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
size_t v_x_22052__boxed_2346_; lean_object* v_res_2347_; 
v_x_22052__boxed_2346_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2347_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2343_, v_x_22052__boxed_2346_, v_x_2345_);
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
size_t v_x_22277__boxed_2439_; lean_object* v_res_2440_; 
v_x_22277__boxed_2439_ = lean_unbox_usize(v_x_2437_);
lean_dec(v_x_2437_);
v_res_2440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2436_, v_x_22277__boxed_2439_, v_x_2438_);
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
v___x_2523_ = lean_st_ref_set(v___y_2454_, v___x_2522_);
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
size_t v_x_22582__boxed_2669_; lean_object* v_res_2670_; 
v_x_22582__boxed_2669_ = lean_unbox_usize(v_x_2667_);
lean_dec(v_x_2667_);
v_res_2670_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2665_, v_x_2666_, v_x_22582__boxed_2669_, v_x_2668_);
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
size_t v_x_22593__boxed_2680_; lean_object* v_res_2681_; 
v_x_22593__boxed_2680_ = lean_unbox_usize(v_x_2678_);
lean_dec(v_x_2678_);
v_res_2681_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2676_, v_x_2677_, v_x_22593__boxed_2680_, v_x_2679_);
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
size_t v_x_27742__boxed_2747_; lean_object* v_res_2748_; 
v_x_27742__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v_x_27742__boxed_2747_, v_x_2746_);
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
lean_object* v_ks_2860_; lean_object* v_vs_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2881_; 
v_ks_2860_ = lean_ctor_get(v_x_2809_, 0);
v_vs_2861_ = lean_ctor_get(v_x_2809_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2863_ = v_x_2809_;
v_isShared_2864_ = v_isSharedCheck_2881_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_vs_2861_);
lean_inc(v_ks_2860_);
lean_dec(v_x_2809_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2881_;
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
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_ks_2860_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_vs_2861_);
v___x_2866_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v_newNode_2867_; uint8_t v___y_2869_; size_t v___x_2875_; uint8_t v___x_2876_; 
v_newNode_2867_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2808_, v___x_2866_, v_x_2812_, v_x_2813_);
v___x_2875_ = ((size_t)7ULL);
v___x_2876_ = lean_usize_dec_le(v___x_2875_, v_x_2811_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2877_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2867_);
v___x_2878_ = lean_unsigned_to_nat(4u);
v___x_2879_ = lean_nat_dec_lt(v___x_2877_, v___x_2878_);
lean_dec(v___x_2877_);
v___y_2869_ = v___x_2879_;
goto v___jp_2868_;
}
else
{
v___y_2869_ = v___x_2876_;
goto v___jp_2868_;
}
v___jp_2868_:
{
if (v___y_2869_ == 0)
{
lean_object* v_ks_2870_; lean_object* v_vs_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_ks_2870_ = lean_ctor_get(v_newNode_2867_, 0);
lean_inc_ref(v_ks_2870_);
v_vs_2871_ = lean_ctor_get(v_newNode_2867_, 1);
lean_inc_ref(v_vs_2871_);
lean_dec_ref(v_newNode_2867_);
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2808_, v_x_2811_, v_ks_2870_, v_vs_2871_, v___x_2872_, v___x_2873_);
lean_dec_ref(v_vs_2871_);
lean_dec_ref(v_ks_2870_);
return v___x_2874_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2882_, size_t v_depth_2883_, lean_object* v_keys_2884_, lean_object* v_vals_2885_, lean_object* v_i_2886_, lean_object* v_entries_2887_){
_start:
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = lean_array_get_size(v_keys_2884_);
v___x_2889_ = lean_nat_dec_lt(v_i_2886_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_dec(v_i_2886_);
return v_entries_2887_;
}
else
{
lean_object* v_k_2890_; lean_object* v_v_2891_; uint64_t v___x_2892_; size_t v_h_2893_; size_t v___x_2894_; lean_object* v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; size_t v_h_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_k_2890_ = lean_array_fget_borrowed(v_keys_2884_, v_i_2886_);
v_v_2891_ = lean_array_fget_borrowed(v_vals_2885_, v_i_2886_);
lean_inc_n(v_k_2890_, 2);
v___x_2892_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2882_, v_k_2890_);
v_h_2893_ = lean_uint64_to_usize(v___x_2892_);
v___x_2894_ = ((size_t)5ULL);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_sub(v_depth_2883_, v___x_2896_);
v___x_2898_ = lean_usize_mul(v___x_2894_, v___x_2897_);
v_h_2899_ = lean_usize_shift_right(v_h_2893_, v___x_2898_);
v___x_2900_ = lean_nat_add(v_i_2886_, v___x_2895_);
lean_dec(v_i_2886_);
lean_inc(v_v_2891_);
v___x_2901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2882_, v_entries_2887_, v_h_2899_, v_depth_2883_, v_k_2890_, v_v_2891_);
v_i_2886_ = v___x_2900_;
v_entries_2887_ = v___x_2901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2903_, lean_object* v_depth_2904_, lean_object* v_keys_2905_, lean_object* v_vals_2906_, lean_object* v_i_2907_, lean_object* v_entries_2908_){
_start:
{
size_t v_depth_boxed_2909_; lean_object* v_res_2910_; 
v_depth_boxed_2909_ = lean_unbox_usize(v_depth_2904_);
lean_dec(v_depth_2904_);
v_res_2910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2903_, v_depth_boxed_2909_, v_keys_2905_, v_vals_2906_, v_i_2907_, v_entries_2908_);
lean_dec_ref(v_vals_2906_);
lean_dec_ref(v_keys_2905_);
lean_dec_ref(v___x_2903_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
size_t v_x_27896__boxed_2917_; size_t v_x_27897__boxed_2918_; lean_object* v_res_2919_; 
v_x_27896__boxed_2917_ = lean_unbox_usize(v_x_2913_);
lean_dec(v_x_2913_);
v_x_27897__boxed_2918_ = lean_unbox_usize(v_x_2914_);
lean_dec(v_x_2914_);
v_res_2919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2911_, v_x_2912_, v_x_27896__boxed_2917_, v_x_27897__boxed_2918_, v_x_2915_, v_x_2916_);
lean_dec_ref(v___x_2911_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
uint64_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
lean_inc_ref(v_x_2922_);
v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2920_, v_x_2922_);
v___x_2925_ = lean_uint64_to_usize(v___x_2924_);
v___x_2926_ = ((size_t)1ULL);
v___x_2927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2920_, v_x_2921_, v___x_2925_, v___x_2926_, v_x_2922_, v_x_2923_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2928_, v_x_2929_, v_x_2930_, v_x_2931_);
lean_dec_ref(v___x_2928_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2937_, lean_object* v_rootNew_2938_, uint8_t v_a_2939_, lean_object* v_a_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; lean_object* v_snd_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3118_; 
v___x_2948_ = lean_st_ref_get(v___y_2941_);
v_snd_2949_ = lean_ctor_get(v_a_2940_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v_a_2940_, 0);
lean_dec(v_unused_3119_);
v___x_2951_ = v_a_2940_;
v_isShared_2952_ = v_isSharedCheck_3118_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snd_2949_);
lean_dec(v_a_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3118_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; 
lean_inc(v_snd_2949_);
v___x_2953_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2948_, v_snd_2949_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___x_2948_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3109_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_3109_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3109_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_self_2958_; lean_object* v_next_2959_; lean_object* v_congr_2960_; lean_object* v_target_x3f_2961_; lean_object* v_proof_x3f_2962_; uint8_t v_flipped_2963_; lean_object* v_size_2964_; uint8_t v_interpreted_2965_; uint8_t v_ctor_2966_; uint8_t v_hasLambdas_2967_; uint8_t v_heqProofs_2968_; lean_object* v_idx_2969_; lean_object* v_generation_2970_; lean_object* v_mt_2971_; lean_object* v_sTerms_2972_; uint8_t v_funCC_2973_; lean_object* v_ematchDiagSource_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3107_; 
v_self_2958_ = lean_ctor_get(v_a_2954_, 0);
v_next_2959_ = lean_ctor_get(v_a_2954_, 1);
v_congr_2960_ = lean_ctor_get(v_a_2954_, 3);
v_target_x3f_2961_ = lean_ctor_get(v_a_2954_, 4);
v_proof_x3f_2962_ = lean_ctor_get(v_a_2954_, 5);
v_flipped_2963_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12);
v_size_2964_ = lean_ctor_get(v_a_2954_, 6);
v_interpreted_2965_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12 + 1);
v_ctor_2966_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12 + 2);
v_hasLambdas_2967_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12 + 3);
v_heqProofs_2968_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12 + 4);
v_idx_2969_ = lean_ctor_get(v_a_2954_, 7);
v_generation_2970_ = lean_ctor_get(v_a_2954_, 8);
v_mt_2971_ = lean_ctor_get(v_a_2954_, 9);
v_sTerms_2972_ = lean_ctor_get(v_a_2954_, 10);
v_funCC_2973_ = lean_ctor_get_uint8(v_a_2954_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2974_ = lean_ctor_get(v_a_2954_, 11);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_a_2954_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_a_2954_, 2);
lean_dec(v_unused_3108_);
v___x_2976_ = v_a_2954_;
v_isShared_2977_ = v_isSharedCheck_3107_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_ematchDiagSource_2974_);
lean_inc(v_sTerms_2972_);
lean_inc(v_mt_2971_);
lean_inc(v_generation_2970_);
lean_inc(v_idx_2969_);
lean_inc(v_size_2964_);
lean_inc(v_proof_x3f_2962_);
lean_inc(v_target_x3f_2961_);
lean_inc(v_congr_2960_);
lean_inc(v_next_2959_);
lean_inc(v_self_2958_);
lean_dec(v_a_2954_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3107_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___y_2995_; lean_object* v___x_3005_; 
v___x_2978_ = lean_box(0);
lean_inc(v_ematchDiagSource_2974_);
lean_inc(v_sTerms_2972_);
lean_inc(v_mt_2971_);
lean_inc(v_generation_2970_);
lean_inc(v_idx_2969_);
lean_inc(v_size_2964_);
lean_inc(v_proof_x3f_2962_);
lean_inc(v_target_x3f_2961_);
lean_inc_ref(v_rootNew_2938_);
lean_inc_ref(v_next_2959_);
lean_inc_ref(v_self_2958_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 2, v_rootNew_2938_);
v___x_3005_ = v___x_2976_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_self_2958_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_next_2959_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_rootNew_2938_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v_congr_2960_);
lean_ctor_set(v_reuseFailAlloc_3106_, 4, v_target_x3f_2961_);
lean_ctor_set(v_reuseFailAlloc_3106_, 5, v_proof_x3f_2962_);
lean_ctor_set(v_reuseFailAlloc_3106_, 6, v_size_2964_);
lean_ctor_set(v_reuseFailAlloc_3106_, 7, v_idx_2969_);
lean_ctor_set(v_reuseFailAlloc_3106_, 8, v_generation_2970_);
lean_ctor_set(v_reuseFailAlloc_3106_, 9, v_mt_2971_);
lean_ctor_set(v_reuseFailAlloc_3106_, 10, v_sTerms_2972_);
lean_ctor_set(v_reuseFailAlloc_3106_, 11, v_ematchDiagSource_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12, v_flipped_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12 + 1, v_interpreted_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12 + 2, v_ctor_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12 + 3, v_hasLambdas_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12 + 4, v_heqProofs_2968_);
lean_ctor_set_uint8(v_reuseFailAlloc_3106_, sizeof(void*)*12 + 5, v_funCC_2973_);
v___x_3005_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3004_;
}
v___jp_2979_:
{
size_t v___x_2980_; size_t v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = lean_ptr_addr(v_next_2959_);
v___x_2981_ = lean_ptr_addr(v_lhs_2937_);
v___x_2982_ = lean_usize_dec_eq(v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2984_; 
lean_del_object(v___x_2956_);
lean_dec(v_snd_2949_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v_next_2959_);
lean_ctor_set(v___x_2951_, 0, v___x_2978_);
v___x_2984_ = v___x_2951_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_next_2959_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v_a_2940_ = v___x_2984_;
goto _start;
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec_ref(v_next_2959_);
lean_dec_ref(v_rootNew_2938_);
v___x_2987_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2987_);
v___x_2989_ = v___x_2951_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_snd_2949_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2989_);
v___x_2991_ = v___x_2956_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
v___jp_2994_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_dec_ref_known(v___y_2995_, 1);
goto v___jp_2979_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_next_2959_);
lean_del_object(v___x_2956_);
lean_del_object(v___x_2951_);
lean_dec(v_snd_2949_);
lean_dec_ref(v_rootNew_2938_);
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___y_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___y_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___y_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; 
lean_inc_ref(v___x_3005_);
lean_inc_ref(v_self_2958_);
v___x_3006_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2958_, v___x_3005_, v___y_2941_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec_ref_known(v___x_3006_, 1);
if (v_a_2939_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
goto v___jp_2979_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3008_ = lean_unsigned_to_nat(3u);
v___x_3009_ = l_Lean_Expr_isAppOfArity(v_self_2958_, v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
goto v___jp_2979_;
}
else
{
uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3005_);
lean_dec_ref(v___x_3005_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v_toGoalState_3012_; lean_object* v_enodeMap_3013_; lean_object* v_congrTable_3014_; lean_object* v___x_3015_; 
v___x_3011_ = lean_st_ref_get(v___y_2941_);
v_toGoalState_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc_ref(v_toGoalState_3012_);
lean_dec(v___x_3011_);
v_enodeMap_3013_ = lean_ctor_get(v_toGoalState_3012_, 1);
lean_inc_ref(v_enodeMap_3013_);
v_congrTable_3014_ = lean_ctor_get(v_toGoalState_3012_, 4);
lean_inc_ref(v_congrTable_3014_);
lean_dec_ref(v_toGoalState_3012_);
lean_inc_ref(v_self_2958_);
v___x_3015_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3013_, v_congrTable_3014_, v_self_2958_);
lean_dec_ref(v_congrTable_3014_);
lean_dec_ref(v_enodeMap_3013_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
goto v___jp_2979_;
}
else
{
lean_object* v_val_3016_; lean_object* v_fst_3017_; lean_object* v___x_3018_; 
v_val_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v_fst_3017_ = lean_ctor_get(v_val_3016_, 0);
lean_inc(v_fst_3017_);
lean_dec(v_val_3016_);
v___x_3018_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3017_, v___y_2942_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; uint8_t v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = lean_unbox(v_a_3019_);
lean_dec(v_a_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v_toGoalState_3022_; lean_object* v_mvarId_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3097_; 
v___x_3021_ = lean_st_ref_take(v___y_2941_);
v_toGoalState_3022_ = lean_ctor_get(v___x_3021_, 0);
v_mvarId_3023_ = lean_ctor_get(v___x_3021_, 1);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3025_ = v___x_3021_;
v_isShared_3026_ = v_isSharedCheck_3097_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_mvarId_3023_);
lean_inc(v_toGoalState_3022_);
lean_dec(v___x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3097_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_nextDeclIdx_3027_; lean_object* v_enodeMap_3028_; lean_object* v_exprs_3029_; lean_object* v_parents_3030_; lean_object* v_congrTable_3031_; lean_object* v_appMap_3032_; lean_object* v_indicesFound_3033_; lean_object* v_newFacts_3034_; uint8_t v_inconsistent_3035_; lean_object* v_nextIdx_3036_; lean_object* v_newRawFacts_3037_; lean_object* v_facts_3038_; lean_object* v_extThms_3039_; lean_object* v_ematch_3040_; lean_object* v_inj_3041_; lean_object* v_split_3042_; lean_object* v_clean_3043_; lean_object* v_sstates_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3096_; 
v_nextDeclIdx_3027_ = lean_ctor_get(v_toGoalState_3022_, 0);
v_enodeMap_3028_ = lean_ctor_get(v_toGoalState_3022_, 1);
v_exprs_3029_ = lean_ctor_get(v_toGoalState_3022_, 2);
v_parents_3030_ = lean_ctor_get(v_toGoalState_3022_, 3);
v_congrTable_3031_ = lean_ctor_get(v_toGoalState_3022_, 4);
v_appMap_3032_ = lean_ctor_get(v_toGoalState_3022_, 5);
v_indicesFound_3033_ = lean_ctor_get(v_toGoalState_3022_, 6);
v_newFacts_3034_ = lean_ctor_get(v_toGoalState_3022_, 7);
v_inconsistent_3035_ = lean_ctor_get_uint8(v_toGoalState_3022_, sizeof(void*)*17);
v_nextIdx_3036_ = lean_ctor_get(v_toGoalState_3022_, 8);
v_newRawFacts_3037_ = lean_ctor_get(v_toGoalState_3022_, 9);
v_facts_3038_ = lean_ctor_get(v_toGoalState_3022_, 10);
v_extThms_3039_ = lean_ctor_get(v_toGoalState_3022_, 11);
v_ematch_3040_ = lean_ctor_get(v_toGoalState_3022_, 12);
v_inj_3041_ = lean_ctor_get(v_toGoalState_3022_, 13);
v_split_3042_ = lean_ctor_get(v_toGoalState_3022_, 14);
v_clean_3043_ = lean_ctor_get(v_toGoalState_3022_, 15);
v_sstates_3044_ = lean_ctor_get(v_toGoalState_3022_, 16);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_toGoalState_3022_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3046_ = v_toGoalState_3022_;
v_isShared_3047_ = v_isSharedCheck_3096_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_sstates_3044_);
lean_inc(v_clean_3043_);
lean_inc(v_split_3042_);
lean_inc(v_inj_3041_);
lean_inc(v_ematch_3040_);
lean_inc(v_extThms_3039_);
lean_inc(v_facts_3038_);
lean_inc(v_newRawFacts_3037_);
lean_inc(v_nextIdx_3036_);
lean_inc(v_newFacts_3034_);
lean_inc(v_indicesFound_3033_);
lean_inc(v_appMap_3032_);
lean_inc(v_congrTable_3031_);
lean_inc(v_parents_3030_);
lean_inc(v_exprs_3029_);
lean_inc(v_enodeMap_3028_);
lean_inc(v_nextDeclIdx_3027_);
lean_dec(v_toGoalState_3022_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3096_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = lean_box(0);
lean_inc_ref(v_self_2958_);
v___x_3049_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3028_, v_congrTable_3031_, v_self_2958_, v___x_3048_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 4, v___x_3049_);
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_nextDeclIdx_3027_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_enodeMap_3028_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_exprs_3029_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_parents_3030_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3095_, 5, v_appMap_3032_);
lean_ctor_set(v_reuseFailAlloc_3095_, 6, v_indicesFound_3033_);
lean_ctor_set(v_reuseFailAlloc_3095_, 7, v_newFacts_3034_);
lean_ctor_set(v_reuseFailAlloc_3095_, 8, v_nextIdx_3036_);
lean_ctor_set(v_reuseFailAlloc_3095_, 9, v_newRawFacts_3037_);
lean_ctor_set(v_reuseFailAlloc_3095_, 10, v_facts_3038_);
lean_ctor_set(v_reuseFailAlloc_3095_, 11, v_extThms_3039_);
lean_ctor_set(v_reuseFailAlloc_3095_, 12, v_ematch_3040_);
lean_ctor_set(v_reuseFailAlloc_3095_, 13, v_inj_3041_);
lean_ctor_set(v_reuseFailAlloc_3095_, 14, v_split_3042_);
lean_ctor_set(v_reuseFailAlloc_3095_, 15, v_clean_3043_);
lean_ctor_set(v_reuseFailAlloc_3095_, 16, v_sstates_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*17, v_inconsistent_3035_);
v___x_3051_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3053_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3051_);
v___x_3053_ = v___x_3025_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_mvarId_3023_);
v___x_3053_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = lean_st_ref_set(v___y_2941_, v___x_3053_);
lean_inc_ref(v_rootNew_2938_);
lean_inc_ref(v_next_2959_);
lean_inc_ref_n(v_self_2958_, 3);
v___x_3055_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3055_, 0, v_self_2958_);
lean_ctor_set(v___x_3055_, 1, v_next_2959_);
lean_ctor_set(v___x_3055_, 2, v_rootNew_2938_);
lean_ctor_set(v___x_3055_, 3, v_self_2958_);
lean_ctor_set(v___x_3055_, 4, v_target_x3f_2961_);
lean_ctor_set(v___x_3055_, 5, v_proof_x3f_2962_);
lean_ctor_set(v___x_3055_, 6, v_size_2964_);
lean_ctor_set(v___x_3055_, 7, v_idx_2969_);
lean_ctor_set(v___x_3055_, 8, v_generation_2970_);
lean_ctor_set(v___x_3055_, 9, v_mt_2971_);
lean_ctor_set(v___x_3055_, 10, v_sTerms_2972_);
lean_ctor_set(v___x_3055_, 11, v_ematchDiagSource_2974_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12, v_flipped_2963_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12 + 1, v_interpreted_2965_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12 + 2, v_ctor_2966_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12 + 3, v_hasLambdas_2967_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12 + 4, v_heqProofs_2968_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*12 + 5, v_funCC_2973_);
v___x_3056_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2958_, v___x_3055_, v___y_2941_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref_known(v___x_3056_, 1);
v___x_3057_ = lean_st_ref_get(v___y_2941_);
lean_inc(v_fst_3017_);
v___x_3058_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3057_, v_fst_3017_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___x_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v_self_3060_; lean_object* v_next_3061_; lean_object* v_root_3062_; lean_object* v_target_x3f_3063_; lean_object* v_proof_x3f_3064_; uint8_t v_flipped_3065_; lean_object* v_size_3066_; uint8_t v_interpreted_3067_; uint8_t v_ctor_3068_; uint8_t v_hasLambdas_3069_; uint8_t v_heqProofs_3070_; lean_object* v_idx_3071_; lean_object* v_generation_3072_; lean_object* v_mt_3073_; lean_object* v_sTerms_3074_; uint8_t v_funCC_3075_; lean_object* v_ematchDiagSource_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v_self_3060_ = lean_ctor_get(v_a_3059_, 0);
v_next_3061_ = lean_ctor_get(v_a_3059_, 1);
v_root_3062_ = lean_ctor_get(v_a_3059_, 2);
v_target_x3f_3063_ = lean_ctor_get(v_a_3059_, 4);
v_proof_x3f_3064_ = lean_ctor_get(v_a_3059_, 5);
v_flipped_3065_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12);
v_size_3066_ = lean_ctor_get(v_a_3059_, 6);
v_interpreted_3067_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12 + 1);
v_ctor_3068_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12 + 2);
v_hasLambdas_3069_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12 + 3);
v_heqProofs_3070_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12 + 4);
v_idx_3071_ = lean_ctor_get(v_a_3059_, 7);
v_generation_3072_ = lean_ctor_get(v_a_3059_, 8);
v_mt_3073_ = lean_ctor_get(v_a_3059_, 9);
v_sTerms_3074_ = lean_ctor_get(v_a_3059_, 10);
v_funCC_3075_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3076_ = lean_ctor_get(v_a_3059_, 11);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_a_3059_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v_a_3059_, 3);
lean_dec(v_unused_3085_);
v___x_3078_ = v_a_3059_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_ematchDiagSource_3076_);
lean_inc(v_sTerms_3074_);
lean_inc(v_mt_3073_);
lean_inc(v_generation_3072_);
lean_inc(v_idx_3071_);
lean_inc(v_size_3066_);
lean_inc(v_proof_x3f_3064_);
lean_inc(v_target_x3f_3063_);
lean_inc(v_root_3062_);
lean_inc(v_next_3061_);
lean_inc(v_self_3060_);
lean_dec(v_a_3059_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 3, v_self_2958_);
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_self_3060_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_next_3061_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_root_3062_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_self_2958_);
lean_ctor_set(v_reuseFailAlloc_3083_, 4, v_target_x3f_3063_);
lean_ctor_set(v_reuseFailAlloc_3083_, 5, v_proof_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3083_, 6, v_size_3066_);
lean_ctor_set(v_reuseFailAlloc_3083_, 7, v_idx_3071_);
lean_ctor_set(v_reuseFailAlloc_3083_, 8, v_generation_3072_);
lean_ctor_set(v_reuseFailAlloc_3083_, 9, v_mt_3073_);
lean_ctor_set(v_reuseFailAlloc_3083_, 10, v_sTerms_3074_);
lean_ctor_set(v_reuseFailAlloc_3083_, 11, v_ematchDiagSource_3076_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12, v_flipped_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12 + 1, v_interpreted_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12 + 2, v_ctor_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12 + 3, v_hasLambdas_3069_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12 + 4, v_heqProofs_3070_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*12 + 5, v_funCC_3075_);
v___x_3081_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3017_, v___x_3081_, v___y_2941_);
v___y_2995_ = v___x_3082_;
goto v___jp_2994_;
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_fst_3017_);
lean_dec_ref(v_next_2959_);
lean_dec_ref(v_self_2958_);
lean_del_object(v___x_2956_);
lean_del_object(v___x_2951_);
lean_dec(v_snd_2949_);
lean_dec_ref(v_rootNew_2938_);
v_a_3086_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3058_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3058_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_dec(v_fst_3017_);
lean_dec_ref(v_self_2958_);
v___y_2995_ = v___x_3056_;
goto v___jp_2994_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3017_);
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
goto v___jp_2979_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_fst_3017_);
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_next_2959_);
lean_dec_ref(v_self_2958_);
lean_del_object(v___x_2956_);
lean_del_object(v___x_2951_);
lean_dec(v_snd_2949_);
lean_dec_ref(v_rootNew_2938_);
v_a_3098_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3018_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3018_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
goto v___jp_2979_;
}
}
}
}
else
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2974_);
lean_dec(v_sTerms_2972_);
lean_dec(v_mt_2971_);
lean_dec(v_generation_2970_);
lean_dec(v_idx_2969_);
lean_dec(v_size_2964_);
lean_dec(v_proof_x3f_2962_);
lean_dec(v_target_x3f_2961_);
lean_dec_ref(v_self_2958_);
v___y_2995_ = v___x_3006_;
goto v___jp_2994_;
}
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_2951_);
lean_dec(v_snd_2949_);
lean_dec_ref(v_rootNew_2938_);
v_a_3110_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_2953_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_2953_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3120_, lean_object* v_rootNew_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
uint8_t v_a_28084__boxed_3131_; lean_object* v_res_3132_; 
v_a_28084__boxed_3131_ = lean_unbox(v_a_3122_);
v_res_3132_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3120_, v_rootNew_3121_, v_a_28084__boxed_3131_, v_a_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_lhs_3120_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3133_, lean_object* v_rootNew_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3134_, v_a_3139_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = lean_box(0);
lean_inc_ref(v_lhs_3133_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v_lhs_3133_);
v___x_3150_ = lean_unbox(v_a_3147_);
lean_dec(v_a_3147_);
v___x_3151_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3133_, v_rootNew_3134_, v___x_3150_, v___x_3149_, v_a_3135_, v_a_3139_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec_ref(v_lhs_3133_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3165_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3165_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3165_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v_fst_3156_; 
v_fst_3156_ = lean_ctor_get(v_a_3152_, 0);
lean_inc(v_fst_3156_);
lean_dec(v_a_3152_);
if (lean_obj_tag(v_fst_3156_) == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = lean_box(0);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3157_);
v___x_3159_ = v___x_3154_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
else
{
lean_object* v_val_3161_; lean_object* v___x_3163_; 
v_val_3161_ = lean_ctor_get(v_fst_3156_, 0);
lean_inc(v_val_3161_);
lean_dec_ref_known(v_fst_3156_, 1);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v_val_3161_);
v___x_3163_ = v___x_3154_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_val_3161_);
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
v_a_3166_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3151_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3151_);
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
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v_rootNew_3134_);
lean_dec_ref(v_lhs_3133_);
v_a_3174_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3146_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3146_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3182_, lean_object* v_rootNew_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3182_, v_rootNew_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec(v_a_3184_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3196_, lean_object* v_00_u03b2_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3196_, v_x_3198_, v_x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3201_, v_00_u03b2_3202_, v_x_3203_, v_x_3204_);
lean_dec_ref(v_x_3203_);
lean_dec_ref(v___x_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3206_, lean_object* v_00_u03b2_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3206_, v_x_3208_, v_x_3209_, v_x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3212_, lean_object* v_00_u03b2_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3212_, v_00_u03b2_3213_, v_x_3214_, v_x_3215_, v_x_3216_);
lean_dec_ref(v___x_3212_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3218_, lean_object* v_rootNew_3219_, uint8_t v_a_3220_, lean_object* v_inst_3221_, lean_object* v_a_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3218_, v_rootNew_3219_, v_a_3220_, v_a_3222_, v___y_3223_, v___y_3227_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3235_, lean_object* v_rootNew_3236_, lean_object* v_a_3237_, lean_object* v_inst_3238_, lean_object* v_a_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_a_28443__boxed_3251_; lean_object* v_res_3252_; 
v_a_28443__boxed_3251_ = lean_unbox(v_a_3237_);
v_res_3252_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3235_, v_rootNew_3236_, v_a_28443__boxed_3251_, v_inst_3238_, v_a_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v_lhs_3235_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3253_, lean_object* v_00_u03b2_3254_, lean_object* v_x_3255_, size_t v_x_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
lean_inc_ref(v_x_3255_);
v___x_3258_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3253_, v_x_3255_, v_x_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3259_, lean_object* v_00_u03b2_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
size_t v_x_28486__boxed_3264_; lean_object* v_res_3265_; 
v_x_28486__boxed_3264_ = lean_unbox_usize(v_x_3262_);
lean_dec(v_x_3262_);
v_res_3265_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3259_, v_00_u03b2_3260_, v_x_3261_, v_x_28486__boxed_3264_, v_x_3263_);
lean_dec_ref(v_x_3261_);
lean_dec_ref(v___x_3259_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_x_3268_, size_t v_x_3269_, size_t v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3266_, v_x_3268_, v_x_3269_, v_x_3270_, v_x_3271_, v_x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3274_, lean_object* v_00_u03b2_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
size_t v_x_28500__boxed_3281_; size_t v_x_28501__boxed_3282_; lean_object* v_res_3283_; 
v_x_28500__boxed_3281_ = lean_unbox_usize(v_x_3277_);
lean_dec(v_x_3277_);
v_x_28501__boxed_3282_ = lean_unbox_usize(v_x_3278_);
lean_dec(v_x_3278_);
v_res_3283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3274_, v_00_u03b2_3275_, v_x_3276_, v_x_28500__boxed_3281_, v_x_28501__boxed_3282_, v_x_3279_, v_x_3280_);
lean_dec_ref(v___x_3274_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3284_, lean_object* v_00_u03b2_3285_, lean_object* v_keys_3286_, lean_object* v_vals_3287_, lean_object* v_heq_3288_, lean_object* v_i_3289_, lean_object* v_k_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3284_, v_keys_3286_, v_vals_3287_, v_i_3289_, v_k_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_keys_3294_, lean_object* v_vals_3295_, lean_object* v_heq_3296_, lean_object* v_i_3297_, lean_object* v_k_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3292_, v_00_u03b2_3293_, v_keys_3294_, v_vals_3295_, v_heq_3296_, v_i_3297_, v_k_3298_);
lean_dec_ref(v_vals_3295_);
lean_dec_ref(v_keys_3294_);
lean_dec_ref(v___x_3292_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3300_, lean_object* v_00_u03b2_3301_, lean_object* v_n_3302_, lean_object* v_k_3303_, lean_object* v_v_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3300_, v_n_3302_, v_k_3303_, v_v_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3306_, lean_object* v_00_u03b2_3307_, lean_object* v_n_3308_, lean_object* v_k_3309_, lean_object* v_v_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3306_, v_00_u03b2_3307_, v_n_3308_, v_k_3309_, v_v_3310_);
lean_dec_ref(v___x_3306_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3312_, lean_object* v_00_u03b2_3313_, size_t v_depth_3314_, lean_object* v_keys_3315_, lean_object* v_vals_3316_, lean_object* v_heq_3317_, lean_object* v_i_3318_, lean_object* v_entries_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3312_, v_depth_3314_, v_keys_3315_, v_vals_3316_, v_i_3318_, v_entries_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3321_, lean_object* v_00_u03b2_3322_, lean_object* v_depth_3323_, lean_object* v_keys_3324_, lean_object* v_vals_3325_, lean_object* v_heq_3326_, lean_object* v_i_3327_, lean_object* v_entries_3328_){
_start:
{
size_t v_depth_boxed_3329_; lean_object* v_res_3330_; 
v_depth_boxed_3329_ = lean_unbox_usize(v_depth_3323_);
lean_dec(v_depth_3323_);
v_res_3330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3321_, v_00_u03b2_3322_, v_depth_boxed_3329_, v_keys_3324_, v_vals_3325_, v_heq_3326_, v_i_3327_, v_entries_3328_);
lean_dec_ref(v_vals_3325_);
lean_dec_ref(v_keys_3324_);
lean_dec_ref(v___x_3321_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3331_, lean_object* v_00_u03b2_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3331_, v_x_3333_, v_x_3334_, v_x_3335_, v_x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3338_, lean_object* v_00_u03b2_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3338_, v_00_u03b2_3339_, v_x_3340_, v_x_3341_, v_x_3342_, v_x_3343_);
lean_dec_ref(v___x_3338_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
if (lean_obj_tag(v_as_x27_3345_) == 0)
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_b_3346_);
return v___x_3358_;
}
else
{
lean_object* v_head_3359_; lean_object* v_tail_3360_; lean_object* v___x_3361_; 
v_head_3359_ = lean_ctor_get(v_as_x27_3345_, 0);
v_tail_3360_ = lean_ctor_get(v_as_x27_3345_, 1);
lean_inc(v_head_3359_);
v___x_3361_ = l_Lean_Meta_Grind_propagateUp(v_head_3359_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref_known(v___x_3361_, 1);
v___x_3362_ = lean_box(0);
v_as_x27_3345_ = v_tail_3360_;
v_b_3346_ = v___x_3362_;
goto _start;
}
else
{
return v___x_3361_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3364_, lean_object* v_b_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3364_, v_b_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v_as_x27_3364_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3378_, lean_object* v_b_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
if (lean_obj_tag(v_as_x27_3378_) == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v_b_3379_);
return v___x_3391_;
}
else
{
lean_object* v_head_3392_; lean_object* v_tail_3393_; lean_object* v___x_3394_; 
v_head_3392_ = lean_ctor_get(v_as_x27_3378_, 0);
v_tail_3393_ = lean_ctor_get(v_as_x27_3378_, 1);
lean_inc(v_head_3392_);
v___x_3394_ = l_Lean_Meta_Grind_propagateDown(v_head_3392_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v___x_3395_; 
lean_dec_ref_known(v___x_3394_, 1);
v___x_3395_ = lean_box(0);
v_as_x27_3378_ = v_tail_3393_;
v_b_3379_ = v___x_3395_;
goto _start;
}
else
{
return v___x_3394_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3397_, v_b_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec(v_as_x27_3397_);
return v_res_3410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_cls_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3415_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3416_ = l_Lean_Name_append(v___x_3415_, v_cls_3414_);
return v___x_3416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
return v___x_3419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3429_, uint8_t v_isHEq_3430_, lean_object* v_lhs_3431_, lean_object* v_rhs_3432_, lean_object* v_lhsNode_3433_, lean_object* v_rhsNode_3434_, lean_object* v_lhsRoot_3435_, lean_object* v_rhsRoot_3436_, uint8_t v_flipped_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; uint8_t v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3567_; uint8_t v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; uint8_t v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; uint8_t v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v_options_3687_; lean_object* v_inheritedTraceOptions_3688_; uint8_t v_hasTrace_3689_; lean_object* v_cls_3690_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v_fns_u2082_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_fns_u2081_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; 
v_options_3687_ = lean_ctor_get(v_a_3446_, 2);
v_inheritedTraceOptions_3688_ = lean_ctor_get(v_a_3446_, 13);
v_hasTrace_3689_ = lean_ctor_get_uint8(v_options_3687_, sizeof(void*)*1);
v_cls_3690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3689_ == 0)
{
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
v___y_3817_ = v_a_3446_;
v___y_3818_ = v_a_3447_;
goto v___jp_3808_;
}
else
{
lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3688_, v_options_3687_, v___x_3889_);
if (v___x_3890_ == 0)
{
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
v___y_3817_ = v_a_3446_;
v___y_3818_ = v_a_3447_;
goto v___jp_3808_;
}
else
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Meta_Grind_updateLastTag(v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v___x_3892_; 
lean_dec_ref_known(v___x_3891_, 1);
lean_inc_ref(v_lhs_3431_);
v___x_3892_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3431_, v_a_3438_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
lean_inc_ref(v_rhs_3432_);
v___x_3894_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3432_, v_a_3438_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v_a_3893_);
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v_a_3895_);
v___x_3901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3690_, v___x_3900_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_dec_ref_known(v___x_3901_, 1);
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
v___y_3817_ = v_a_3446_;
v___y_3818_ = v_a_3447_;
goto v___jp_3808_;
}
else
{
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhsNode_3433_);
lean_dec_ref(v_rhs_3432_);
lean_dec_ref(v_lhs_3431_);
lean_dec_ref(v_proof_3429_);
return v___x_3901_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_a_3893_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhsNode_3433_);
lean_dec_ref(v_rhs_3432_);
lean_dec_ref(v_lhs_3431_);
lean_dec_ref(v_proof_3429_);
v_a_3902_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3894_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3894_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhsNode_3433_);
lean_dec_ref(v_rhs_3432_);
lean_dec_ref(v_lhs_3431_);
lean_dec_ref(v_proof_3429_);
v_a_3910_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3892_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3892_);
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
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhsNode_3433_);
lean_dec_ref(v_rhs_3432_);
lean_dec_ref(v_lhs_3431_);
lean_dec_ref(v_proof_3429_);
return v___x_3891_;
}
}
}
v___jp_3449_:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3456_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3492_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3492_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3492_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_unbox(v_a_3467_);
lean_dec(v_a_3467_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_del_object(v___x_3469_);
v___x_3472_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3450_);
lean_dec(v___y_3450_);
v___x_3473_ = lean_box(0);
v___x_3474_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3472_, v___x_3473_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___x_3472_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3474_, 1);
v___x_3475_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3455_, v___x_3473_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref_known(v___x_3475_, 1);
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3453_, v___y_3452_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3453_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref_known(v___x_3476_, 1);
v___x_3477_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3451_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3486_; 
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3487_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
uint8_t v___x_3481_; 
v___x_3481_ = l_Lean_Expr_isTrue(v___y_3454_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3483_; 
lean_dec(v___y_3455_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3473_);
v___x_3483_ = v___x_3479_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3473_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
else
{
lean_object* v___x_3485_; 
lean_del_object(v___x_3479_);
v___x_3485_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3455_);
return v___x_3485_;
}
}
}
else
{
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
return v___x_3477_;
}
}
else
{
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3451_);
return v___x_3476_;
}
}
else
{
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
return v___x_3475_;
}
}
else
{
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
return v___x_3474_;
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
v___x_3488_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3488_);
v___x_3490_ = v___x_3469_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
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
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
v_a_3493_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3466_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3466_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
v___jp_3501_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_inc_ref(v___y_3512_);
v___x_3538_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3538_, 0, v___y_3512_);
lean_ctor_set(v___x_3538_, 1, v___y_3536_);
lean_ctor_set(v___x_3538_, 2, v___y_3518_);
lean_ctor_set(v___x_3538_, 3, v___y_3502_);
lean_ctor_set(v___x_3538_, 4, v___y_3534_);
lean_ctor_set(v___x_3538_, 5, v___y_3516_);
lean_ctor_set(v___x_3538_, 6, v___y_3532_);
lean_ctor_set(v___x_3538_, 7, v___y_3509_);
lean_ctor_set(v___x_3538_, 8, v___y_3517_);
lean_ctor_set(v___x_3538_, 9, v___y_3528_);
lean_ctor_set(v___x_3538_, 10, v___y_3521_);
lean_ctor_set(v___x_3538_, 11, v___y_3505_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12, v___y_3504_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12 + 1, v___y_3529_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12 + 2, v___y_3520_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12 + 3, v___y_3531_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12 + 4, v___y_3537_);
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*12 + 5, v___y_3513_);
lean_inc_ref(v___y_3535_);
v___x_3539_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3535_, v___x_3538_, v___y_3507_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref_known(v___x_3539_, 1);
lean_inc_ref(v___y_3523_);
v___x_3540_ = l_Lean_Meta_Grind_propagateBeta(v___y_3523_, v___y_3522_, v___y_3507_, v___y_3506_, v___y_3514_, v___y_3510_, v___y_3533_, v___y_3527_, v___y_3515_, v___y_3508_, v___y_3526_, v___y_3511_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3541_; 
lean_dec_ref_known(v___x_3540_, 1);
lean_inc_ref(v___y_3519_);
v___x_3541_ = l_Lean_Meta_Grind_propagateBeta(v___y_3519_, v___y_3530_, v___y_3507_, v___y_3506_, v___y_3514_, v___y_3510_, v___y_3533_, v___y_3527_, v___y_3515_, v___y_3508_, v___y_3526_, v___y_3511_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v___x_3542_; 
lean_dec_ref_known(v___x_3541_, 1);
v___x_3542_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3436_, v_lhsRoot_3435_, v___y_3507_, v___y_3515_, v___y_3508_, v___y_3526_, v___y_3511_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3544_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3525_, v___y_3507_);
lean_dec_ref(v___y_3525_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v___x_3545_; 
lean_dec_ref_known(v___x_3544_, 1);
lean_inc_ref(v___y_3535_);
v___x_3545_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3503_, v___y_3535_, v___y_3507_, v___y_3506_, v___y_3514_, v___y_3510_, v___y_3533_, v___y_3527_, v___y_3515_, v___y_3508_, v___y_3526_, v___y_3511_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3545_, 1);
v___x_3546_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3507_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; uint8_t v___x_3548_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = lean_unbox(v_a_3547_);
lean_dec(v_a_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3512_, v___y_3507_, v___y_3506_, v___y_3514_, v___y_3510_, v___y_3533_, v___y_3527_, v___y_3515_, v___y_3508_, v___y_3526_, v___y_3511_);
lean_dec_ref(v___y_3512_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref_known(v___x_3549_, 1);
v___y_3450_ = v___y_3503_;
v___y_3451_ = v_a_3543_;
v___y_3452_ = v___y_3519_;
v___y_3453_ = v___y_3523_;
v___y_3454_ = v___y_3535_;
v___y_3455_ = v___y_3524_;
v___y_3456_ = v___y_3507_;
v___y_3457_ = v___y_3506_;
v___y_3458_ = v___y_3514_;
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3533_;
v___y_3461_ = v___y_3527_;
v___y_3462_ = v___y_3515_;
v___y_3463_ = v___y_3508_;
v___y_3464_ = v___y_3526_;
v___y_3465_ = v___y_3511_;
goto v___jp_3449_;
}
else
{
lean_dec(v_a_3543_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3503_);
return v___x_3549_;
}
}
else
{
lean_dec_ref(v___y_3512_);
v___y_3450_ = v___y_3503_;
v___y_3451_ = v_a_3543_;
v___y_3452_ = v___y_3519_;
v___y_3453_ = v___y_3523_;
v___y_3454_ = v___y_3535_;
v___y_3455_ = v___y_3524_;
v___y_3456_ = v___y_3507_;
v___y_3457_ = v___y_3506_;
v___y_3458_ = v___y_3514_;
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3533_;
v___y_3461_ = v___y_3527_;
v___y_3462_ = v___y_3515_;
v___y_3463_ = v___y_3508_;
v___y_3464_ = v___y_3526_;
v___y_3465_ = v___y_3511_;
goto v___jp_3449_;
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_a_3543_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
v_a_3550_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3546_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3546_);
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
lean_dec(v_a_3543_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
return v___x_3545_;
}
}
else
{
lean_dec(v_a_3543_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
return v___x_3544_;
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
v_a_3558_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3542_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3542_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
return v___x_3541_;
}
}
else
{
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
return v___x_3540_;
}
}
else
{
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3503_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
return v___x_3539_;
}
}
v___jp_3566_:
{
if (v_isHEq_3430_ == 0)
{
if (v___y_3573_ == 0)
{
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3591_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3603_;
v___y_3532_ = v___y_3597_;
v___y_3533_ = v___y_3600_;
v___y_3534_ = v___y_3599_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3598_;
goto v___jp_3501_;
}
else
{
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3591_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3603_;
v___y_3532_ = v___y_3597_;
v___y_3533_ = v___y_3600_;
v___y_3534_ = v___y_3599_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3573_;
goto v___jp_3501_;
}
}
else
{
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3591_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3603_;
v___y_3532_ = v___y_3597_;
v___y_3533_ = v___y_3600_;
v___y_3534_ = v___y_3599_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v_isHEq_3430_;
goto v___jp_3501_;
}
}
v___jp_3604_:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3609_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec_ref_known(v___x_3627_, 1);
v___x_3628_ = lean_st_ref_get(v___y_3617_);
v___x_3629_ = lean_st_ref_get(v___y_3617_);
lean_inc_ref(v___y_3606_);
v___x_3630_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3629_, v___y_3606_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___x_3629_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_self_3632_; lean_object* v_root_3633_; lean_object* v_congr_3634_; lean_object* v_target_x3f_3635_; lean_object* v_proof_x3f_3636_; uint8_t v_flipped_3637_; lean_object* v_size_3638_; uint8_t v_interpreted_3639_; uint8_t v_ctor_3640_; uint8_t v_hasLambdas_3641_; uint8_t v_heqProofs_3642_; lean_object* v_idx_3643_; lean_object* v_generation_3644_; lean_object* v_mt_3645_; lean_object* v_sTerms_3646_; uint8_t v_funCC_3647_; lean_object* v_ematchDiagSource_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3677_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_self_3632_ = lean_ctor_get(v_a_3631_, 0);
v_root_3633_ = lean_ctor_get(v_a_3631_, 2);
v_congr_3634_ = lean_ctor_get(v_a_3631_, 3);
v_target_x3f_3635_ = lean_ctor_get(v_a_3631_, 4);
v_proof_x3f_3636_ = lean_ctor_get(v_a_3631_, 5);
v_flipped_3637_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12);
v_size_3638_ = lean_ctor_get(v_a_3631_, 6);
v_interpreted_3639_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 1);
v_ctor_3640_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 2);
v_hasLambdas_3641_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 3);
v_heqProofs_3642_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 4);
v_idx_3643_ = lean_ctor_get(v_a_3631_, 7);
v_generation_3644_ = lean_ctor_get(v_a_3631_, 8);
v_mt_3645_ = lean_ctor_get(v_a_3631_, 9);
v_sTerms_3646_ = lean_ctor_get(v_a_3631_, 10);
v_funCC_3647_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3648_ = lean_ctor_get(v_a_3631_, 11);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_a_3631_, 1);
lean_dec(v_unused_3678_);
v___x_3650_ = v_a_3631_;
v_isShared_3651_ = v_isSharedCheck_3677_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_ematchDiagSource_3648_);
lean_inc(v_sTerms_3646_);
lean_inc(v_mt_3645_);
lean_inc(v_generation_3644_);
lean_inc(v_idx_3643_);
lean_inc(v_size_3638_);
lean_inc(v_proof_x3f_3636_);
lean_inc(v_target_x3f_3635_);
lean_inc(v_congr_3634_);
lean_inc(v_root_3633_);
lean_inc(v_self_3632_);
lean_dec(v_a_3631_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3677_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_self_3652_; lean_object* v_next_3653_; lean_object* v_root_3654_; lean_object* v_congr_3655_; lean_object* v_target_x3f_3656_; lean_object* v_proof_x3f_3657_; uint8_t v_flipped_3658_; lean_object* v_size_3659_; uint8_t v_interpreted_3660_; uint8_t v_ctor_3661_; uint8_t v_hasLambdas_3662_; uint8_t v_heqProofs_3663_; lean_object* v_idx_3664_; lean_object* v_generation_3665_; lean_object* v_mt_3666_; lean_object* v_sTerms_3667_; uint8_t v_funCC_3668_; lean_object* v_ematchDiagSource_3669_; lean_object* v___x_3671_; 
v_self_3652_ = lean_ctor_get(v_rhsRoot_3436_, 0);
v_next_3653_ = lean_ctor_get(v_rhsRoot_3436_, 1);
v_root_3654_ = lean_ctor_get(v_rhsRoot_3436_, 2);
v_congr_3655_ = lean_ctor_get(v_rhsRoot_3436_, 3);
v_target_x3f_3656_ = lean_ctor_get(v_rhsRoot_3436_, 4);
v_proof_x3f_3657_ = lean_ctor_get(v_rhsRoot_3436_, 5);
v_flipped_3658_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12);
v_size_3659_ = lean_ctor_get(v_rhsRoot_3436_, 6);
v_interpreted_3660_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12 + 1);
v_ctor_3661_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12 + 2);
v_hasLambdas_3662_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12 + 3);
v_heqProofs_3663_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12 + 4);
v_idx_3664_ = lean_ctor_get(v_rhsRoot_3436_, 7);
v_generation_3665_ = lean_ctor_get(v_rhsRoot_3436_, 8);
v_mt_3666_ = lean_ctor_get(v_rhsRoot_3436_, 9);
v_sTerms_3667_ = lean_ctor_get(v_rhsRoot_3436_, 10);
v_funCC_3668_ = lean_ctor_get_uint8(v_rhsRoot_3436_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3669_ = lean_ctor_get(v_rhsRoot_3436_, 11);
lean_inc_ref(v_next_3653_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v_next_3653_);
v___x_3671_ = v___x_3650_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_self_3632_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_next_3653_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_root_3633_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_congr_3634_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_target_x3f_3635_);
lean_ctor_set(v_reuseFailAlloc_3676_, 5, v_proof_x3f_3636_);
lean_ctor_set(v_reuseFailAlloc_3676_, 6, v_size_3638_);
lean_ctor_set(v_reuseFailAlloc_3676_, 7, v_idx_3643_);
lean_ctor_set(v_reuseFailAlloc_3676_, 8, v_generation_3644_);
lean_ctor_set(v_reuseFailAlloc_3676_, 9, v_mt_3645_);
lean_ctor_set(v_reuseFailAlloc_3676_, 10, v_sTerms_3646_);
lean_ctor_set(v_reuseFailAlloc_3676_, 11, v_ematchDiagSource_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12, v_flipped_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12 + 1, v_interpreted_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12 + 2, v_ctor_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12 + 3, v_hasLambdas_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12 + 4, v_heqProofs_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3676_, sizeof(void*)*12 + 5, v_funCC_3647_);
v___x_3671_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3616_, v___x_3671_, v___y_3617_);
if (lean_obj_tag(v___x_3672_) == 0)
{
uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3672_, 1);
v___x_3673_ = 0;
v___x_3674_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3628_, v_lhs_3431_, v___x_3673_);
lean_dec(v___x_3628_);
v___x_3675_ = lean_nat_add(v_size_3659_, v___y_3608_);
lean_dec(v___y_3608_);
if (v_hasLambdas_3662_ == 0)
{
lean_inc(v_target_x3f_3656_);
lean_inc(v_mt_3666_);
lean_inc(v_sTerms_3667_);
lean_inc_ref(v_root_3654_);
lean_inc(v_generation_3665_);
lean_inc(v_proof_x3f_3657_);
lean_inc_ref(v_self_3652_);
lean_inc(v_idx_3664_);
lean_inc(v_ematchDiagSource_3669_);
lean_inc_ref(v_congr_3655_);
v___y_3567_ = v_congr_3655_;
v___y_3568_ = v_flipped_3658_;
v___y_3569_ = v___y_3609_;
v___y_3570_ = v___y_3618_;
v___y_3571_ = v_ematchDiagSource_3669_;
v___y_3572_ = v___y_3617_;
v___y_3573_ = v_heqProofs_3663_;
v___y_3574_ = v___y_3624_;
v___y_3575_ = v___y_3620_;
v___y_3576_ = v_idx_3664_;
v___y_3577_ = v___y_3626_;
v___y_3578_ = v_funCC_3668_;
v___y_3579_ = v_self_3652_;
v___y_3580_ = v___y_3619_;
v___y_3581_ = v___y_3623_;
v___y_3582_ = v_proof_x3f_3657_;
v___y_3583_ = v_generation_3665_;
v___y_3584_ = v_root_3654_;
v___y_3585_ = v___y_3612_;
v___y_3586_ = v_ctor_3661_;
v___y_3587_ = v_sTerms_3667_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v___y_3613_;
v___y_3590_ = v___x_3674_;
v___y_3591_ = v___y_3622_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v___y_3606_;
v___y_3594_ = v_mt_3666_;
v___y_3595_ = v_interpreted_3660_;
v___y_3596_ = v___y_3607_;
v___y_3597_ = v___x_3675_;
v___y_3598_ = v___y_3610_;
v___y_3599_ = v_target_x3f_3656_;
v___y_3600_ = v___y_3621_;
v___y_3601_ = v___y_3614_;
v___y_3602_ = v___y_3615_;
v___y_3603_ = v___y_3605_;
goto v___jp_3566_;
}
else
{
lean_inc(v_target_x3f_3656_);
lean_inc(v_mt_3666_);
lean_inc(v_sTerms_3667_);
lean_inc_ref(v_root_3654_);
lean_inc(v_generation_3665_);
lean_inc(v_proof_x3f_3657_);
lean_inc_ref(v_self_3652_);
lean_inc(v_idx_3664_);
lean_inc(v_ematchDiagSource_3669_);
lean_inc_ref(v_congr_3655_);
v___y_3567_ = v_congr_3655_;
v___y_3568_ = v_flipped_3658_;
v___y_3569_ = v___y_3609_;
v___y_3570_ = v___y_3618_;
v___y_3571_ = v_ematchDiagSource_3669_;
v___y_3572_ = v___y_3617_;
v___y_3573_ = v_heqProofs_3663_;
v___y_3574_ = v___y_3624_;
v___y_3575_ = v___y_3620_;
v___y_3576_ = v_idx_3664_;
v___y_3577_ = v___y_3626_;
v___y_3578_ = v_funCC_3668_;
v___y_3579_ = v_self_3652_;
v___y_3580_ = v___y_3619_;
v___y_3581_ = v___y_3623_;
v___y_3582_ = v_proof_x3f_3657_;
v___y_3583_ = v_generation_3665_;
v___y_3584_ = v_root_3654_;
v___y_3585_ = v___y_3612_;
v___y_3586_ = v_ctor_3661_;
v___y_3587_ = v_sTerms_3667_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v___y_3613_;
v___y_3590_ = v___x_3674_;
v___y_3591_ = v___y_3622_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v___y_3606_;
v___y_3594_ = v_mt_3666_;
v___y_3595_ = v_interpreted_3660_;
v___y_3596_ = v___y_3607_;
v___y_3597_ = v___x_3675_;
v___y_3598_ = v___y_3610_;
v___y_3599_ = v_target_x3f_3656_;
v___y_3600_ = v___y_3621_;
v___y_3601_ = v___y_3614_;
v___y_3602_ = v___y_3615_;
v___y_3603_ = v_hasLambdas_3662_;
goto v___jp_3566_;
}
}
else
{
lean_dec(v___x_3628_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v___x_3628_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
v_a_3679_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3630_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3630_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_dec_ref(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
return v___x_3627_;
}
}
v___jp_3691_:
{
lean_object* v_self_3707_; lean_object* v_next_3708_; lean_object* v_size_3709_; uint8_t v_hasLambdas_3710_; uint8_t v_heqProofs_3711_; lean_object* v___x_3712_; 
v_self_3707_ = lean_ctor_get(v_lhsRoot_3435_, 0);
v_next_3708_ = lean_ctor_get(v_lhsRoot_3435_, 1);
v_size_3709_ = lean_ctor_get(v_lhsRoot_3435_, 6);
v_hasLambdas_3710_ = lean_ctor_get_uint8(v_lhsRoot_3435_, sizeof(void*)*12 + 3);
v_heqProofs_3711_ = lean_ctor_get_uint8(v_lhsRoot_3435_, sizeof(void*)*12 + 4);
v___x_3712_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3707_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v_root_3714_; lean_object* v___x_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v_root_3714_ = lean_ctor_get(v_rhsNode_3434_, 2);
lean_inc_ref_n(v_root_3714_, 2);
lean_dec_ref(v_rhsNode_3434_);
lean_inc_ref(v_lhs_3431_);
v___x_3715_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3431_, v_root_3714_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_options_3716_; uint8_t v_hasTrace_3717_; 
lean_dec_ref_known(v___x_3715_, 1);
v_options_3716_ = lean_ctor_get(v___y_3705_, 2);
v_hasTrace_3717_ = lean_ctor_get_uint8(v_options_3716_, sizeof(void*)*1);
if (v_hasTrace_3717_ == 0)
{
lean_inc_ref(v_next_3708_);
lean_inc(v_size_3709_);
lean_inc_ref(v_self_3707_);
v___y_3605_ = v_hasLambdas_3710_;
v___y_3606_ = v_self_3707_;
v___y_3607_ = v_fns_u2082_3696_;
v___y_3608_ = v_size_3709_;
v___y_3609_ = v_a_3713_;
v___y_3610_ = v_heqProofs_3711_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_root_3714_;
v___y_3615_ = v_next_3708_;
v___y_3616_ = v___y_3695_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
goto v___jp_3604_;
}
else
{
lean_object* v_inheritedTraceOptions_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_inheritedTraceOptions_3718_ = lean_ctor_get(v___y_3705_, 13);
v___x_3719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3718_, v_options_3716_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_inc_ref(v_next_3708_);
lean_inc(v_size_3709_);
lean_inc_ref(v_self_3707_);
v___y_3605_ = v_hasLambdas_3710_;
v___y_3606_ = v_self_3707_;
v___y_3607_ = v_fns_u2082_3696_;
v___y_3608_ = v_size_3709_;
v___y_3609_ = v_a_3713_;
v___y_3610_ = v_heqProofs_3711_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_root_3714_;
v___y_3615_ = v_next_3708_;
v___y_3616_ = v___y_3695_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Meta_Grind_updateLastTag(v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; 
lean_dec_ref_known(v___x_3721_, 1);
lean_inc_ref(v_lhs_3431_);
v___x_3722_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3431_, v___y_3697_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
lean_inc_ref(v_root_3714_);
v___x_3724_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3714_, v___y_3697_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = lean_st_ref_get(v___y_3697_);
lean_inc_ref(v_lhs_3431_);
v___x_3727_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3726_, v_lhs_3431_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___x_3726_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3728_, v___y_3697_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_a_3723_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v_a_3725_);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v_a_3730_);
v___x_3737_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3690_, v___x_3736_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_dec_ref_known(v___x_3737_, 1);
lean_inc_ref(v_next_3708_);
lean_inc(v_size_3709_);
lean_inc_ref(v_self_3707_);
v___y_3605_ = v_hasLambdas_3710_;
v___y_3606_ = v_self_3707_;
v___y_3607_ = v_fns_u2082_3696_;
v___y_3608_ = v_size_3709_;
v___y_3609_ = v_a_3713_;
v___y_3610_ = v_heqProofs_3711_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_root_3714_;
v___y_3615_ = v_next_3708_;
v___y_3616_ = v___y_3695_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
goto v___jp_3604_;
}
else
{
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
return v___x_3737_;
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
v_a_3738_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3729_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3729_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
v_a_3746_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3727_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3727_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
v_a_3754_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3724_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3724_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
v_a_3762_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3722_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3722_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
return v___x_3721_;
}
}
}
}
else
{
lean_dec_ref(v_root_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_lhs_3431_);
return v___x_3715_;
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_fns_u2082_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
v_a_3770_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3712_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3712_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
v___jp_3778_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3793_ = lean_array_get_size(v___y_3779_);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_nat_dec_eq(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v_self_3796_; lean_object* v___x_3797_; 
v_self_3796_ = lean_ctor_get(v_lhsRoot_3435_, 0);
lean_inc_ref(v_self_3796_);
v___x_3797_ = l_Lean_Meta_Grind_getFnRoots(v_self_3796_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___y_3692_ = v___y_3779_;
v___y_3693_ = v_fns_u2081_3782_;
v___y_3694_ = v___y_3780_;
v___y_3695_ = v___y_3781_;
v_fns_u2082_3696_ = v_a_3798_;
v___y_3697_ = v___y_3783_;
v___y_3698_ = v___y_3784_;
v___y_3699_ = v___y_3785_;
v___y_3700_ = v___y_3786_;
v___y_3701_ = v___y_3787_;
v___y_3702_ = v___y_3788_;
v___y_3703_ = v___y_3789_;
v___y_3704_ = v___y_3790_;
v___y_3705_ = v___y_3791_;
v___y_3706_ = v___y_3792_;
goto v___jp_3691_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_fns_u2081_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
v_a_3799_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3797_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v___x_3807_; 
v___x_3807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3692_ = v___y_3779_;
v___y_3693_ = v_fns_u2081_3782_;
v___y_3694_ = v___y_3780_;
v___y_3695_ = v___y_3781_;
v_fns_u2082_3696_ = v___x_3807_;
v___y_3697_ = v___y_3783_;
v___y_3698_ = v___y_3784_;
v___y_3699_ = v___y_3785_;
v___y_3700_ = v___y_3786_;
v___y_3701_ = v___y_3787_;
v___y_3702_ = v___y_3788_;
v___y_3703_ = v___y_3789_;
v___y_3704_ = v___y_3790_;
v___y_3705_ = v___y_3791_;
v___y_3706_ = v___y_3792_;
goto v___jp_3691_;
}
}
v___jp_3808_:
{
lean_object* v___x_3819_; 
lean_inc_ref(v_lhs_3431_);
v___x_3819_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3431_, v___y_3809_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3887_; 
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v___x_3819_, 0);
lean_dec(v_unused_3888_);
v___x_3821_ = v___x_3819_;
v_isShared_3822_ = v_isSharedCheck_3887_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v___x_3819_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3887_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_self_3823_; lean_object* v_next_3824_; lean_object* v_root_3825_; lean_object* v_congr_3826_; lean_object* v_size_3827_; uint8_t v_interpreted_3828_; uint8_t v_ctor_3829_; uint8_t v_hasLambdas_3830_; uint8_t v_heqProofs_3831_; lean_object* v_idx_3832_; lean_object* v_generation_3833_; lean_object* v_mt_3834_; lean_object* v_sTerms_3835_; uint8_t v_funCC_3836_; lean_object* v_ematchDiagSource_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3884_; 
v_self_3823_ = lean_ctor_get(v_lhsNode_3433_, 0);
v_next_3824_ = lean_ctor_get(v_lhsNode_3433_, 1);
v_root_3825_ = lean_ctor_get(v_lhsNode_3433_, 2);
v_congr_3826_ = lean_ctor_get(v_lhsNode_3433_, 3);
v_size_3827_ = lean_ctor_get(v_lhsNode_3433_, 6);
v_interpreted_3828_ = lean_ctor_get_uint8(v_lhsNode_3433_, sizeof(void*)*12 + 1);
v_ctor_3829_ = lean_ctor_get_uint8(v_lhsNode_3433_, sizeof(void*)*12 + 2);
v_hasLambdas_3830_ = lean_ctor_get_uint8(v_lhsNode_3433_, sizeof(void*)*12 + 3);
v_heqProofs_3831_ = lean_ctor_get_uint8(v_lhsNode_3433_, sizeof(void*)*12 + 4);
v_idx_3832_ = lean_ctor_get(v_lhsNode_3433_, 7);
v_generation_3833_ = lean_ctor_get(v_lhsNode_3433_, 8);
v_mt_3834_ = lean_ctor_get(v_lhsNode_3433_, 9);
v_sTerms_3835_ = lean_ctor_get(v_lhsNode_3433_, 10);
v_funCC_3836_ = lean_ctor_get_uint8(v_lhsNode_3433_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3837_ = lean_ctor_get(v_lhsNode_3433_, 11);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_lhsNode_3433_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; 
v_unused_3885_ = lean_ctor_get(v_lhsNode_3433_, 5);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_lhsNode_3433_, 4);
lean_dec(v_unused_3886_);
v___x_3839_ = v_lhsNode_3433_;
v_isShared_3840_ = v_isSharedCheck_3884_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_ematchDiagSource_3837_);
lean_inc(v_sTerms_3835_);
lean_inc(v_mt_3834_);
lean_inc(v_generation_3833_);
lean_inc(v_idx_3832_);
lean_inc(v_size_3827_);
lean_inc(v_congr_3826_);
lean_inc(v_root_3825_);
lean_inc(v_next_3824_);
lean_inc(v_self_3823_);
lean_dec(v_lhsNode_3433_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3884_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 1);
lean_ctor_set(v___x_3821_, 0, v_rhs_3432_);
v___x_3842_ = v___x_3821_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_rhs_3432_);
v___x_3842_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_proof_3429_);
lean_inc_ref(v_root_3825_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 5, v___x_3843_);
lean_ctor_set(v___x_3839_, 4, v___x_3842_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_self_3823_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_next_3824_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_root_3825_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_congr_3826_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3882_, 5, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3882_, 6, v_size_3827_);
lean_ctor_set(v_reuseFailAlloc_3882_, 7, v_idx_3832_);
lean_ctor_set(v_reuseFailAlloc_3882_, 8, v_generation_3833_);
lean_ctor_set(v_reuseFailAlloc_3882_, 9, v_mt_3834_);
lean_ctor_set(v_reuseFailAlloc_3882_, 10, v_sTerms_3835_);
lean_ctor_set(v_reuseFailAlloc_3882_, 11, v_ematchDiagSource_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 1, v_interpreted_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 2, v_ctor_3829_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 3, v_hasLambdas_3830_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 4, v_heqProofs_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 5, v_funCC_3836_);
v___x_3845_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*12, v_flipped_3437_);
lean_inc_ref(v_lhs_3431_);
v___x_3846_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3431_, v___x_3845_, v___y_3809_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref_known(v___x_3846_, 1);
v___x_3847_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3435_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3436_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = lean_array_get_size(v_a_3848_);
v___x_3852_ = lean_unsigned_to_nat(0u);
v___x_3853_ = lean_nat_dec_eq(v___x_3851_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v_self_3854_; lean_object* v___x_3855_; 
v_self_3854_ = lean_ctor_get(v_rhsRoot_3436_, 0);
lean_inc_ref(v_self_3854_);
v___x_3855_ = l_Lean_Meta_Grind_getFnRoots(v_self_3854_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___y_3779_ = v_a_3850_;
v___y_3780_ = v_a_3848_;
v___y_3781_ = v_root_3825_;
v_fns_u2081_3782_ = v_a_3856_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v_a_3850_);
lean_dec(v_a_3848_);
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
v_a_3857_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3855_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3855_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_object* v___x_3865_; 
v___x_3865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3779_ = v_a_3850_;
v___y_3780_ = v_a_3848_;
v___y_3781_ = v_root_3825_;
v_fns_u2081_3782_ = v___x_3865_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
goto v___jp_3778_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3848_);
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
v_a_3866_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3849_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3849_);
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
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
v_a_3874_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3847_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3847_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhs_3431_);
return v___x_3846_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3436_);
lean_dec_ref(v_lhsRoot_3435_);
lean_dec_ref(v_rhsNode_3434_);
lean_dec_ref(v_lhsNode_3433_);
lean_dec_ref(v_rhs_3432_);
lean_dec_ref(v_lhs_3431_);
lean_dec_ref(v_proof_3429_);
return v___x_3819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3918_ = _args[0];
lean_object* v_isHEq_3919_ = _args[1];
lean_object* v_lhs_3920_ = _args[2];
lean_object* v_rhs_3921_ = _args[3];
lean_object* v_lhsNode_3922_ = _args[4];
lean_object* v_rhsNode_3923_ = _args[5];
lean_object* v_lhsRoot_3924_ = _args[6];
lean_object* v_rhsRoot_3925_ = _args[7];
lean_object* v_flipped_3926_ = _args[8];
lean_object* v_a_3927_ = _args[9];
lean_object* v_a_3928_ = _args[10];
lean_object* v_a_3929_ = _args[11];
lean_object* v_a_3930_ = _args[12];
lean_object* v_a_3931_ = _args[13];
lean_object* v_a_3932_ = _args[14];
lean_object* v_a_3933_ = _args[15];
lean_object* v_a_3934_ = _args[16];
lean_object* v_a_3935_ = _args[17];
lean_object* v_a_3936_ = _args[18];
lean_object* v_a_3937_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3938_; uint8_t v_flipped_boxed_3939_; lean_object* v_res_3940_; 
v_isHEq_boxed_3938_ = lean_unbox(v_isHEq_3919_);
v_flipped_boxed_3939_ = lean_unbox(v_flipped_3926_);
v_res_3940_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3918_, v_isHEq_boxed_3938_, v_lhs_3920_, v_rhs_3921_, v_lhsNode_3922_, v_rhsNode_3923_, v_lhsRoot_3924_, v_rhsRoot_3925_, v_flipped_boxed_3939_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec(v_a_3927_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3941_, lean_object* v_as_x27_3942_, lean_object* v_b_3943_, lean_object* v_a_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3942_, v_b_3943_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3957_, lean_object* v_as_x27_3958_, lean_object* v_b_3959_, lean_object* v_a_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3957_, v_as_x27_3958_, v_b_3959_, v_a_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec(v_as_x27_3958_);
lean_dec(v_as_3957_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3973_, lean_object* v_as_x27_3974_, lean_object* v_b_3975_, lean_object* v_a_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3974_, v_b_3975_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3989_, lean_object* v_as_x27_3990_, lean_object* v_b_3991_, lean_object* v_a_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3989_, v_as_x27_3990_, v_b_3991_, v_a_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec(v_as_x27_3990_);
lean_dec(v_as_3989_);
return v_res_4004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4007_ = l_Lean_stringToMessageData(v___x_4006_);
return v___x_4007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4013_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4014_ = l_Lean_Name_append(v___x_4013_, v___x_4012_);
return v___x_4014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4017_ = l_Lean_stringToMessageData(v___x_4016_);
return v___x_4017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4020_ = l_Lean_stringToMessageData(v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4021_, lean_object* v_rhs_4022_, lean_object* v_proof_4023_, uint8_t v_isHEq_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_st_ref_get(v_a_4025_);
lean_inc_ref(v_lhs_4021_);
v___x_4040_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4039_, v_lhs_4021_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v___x_4039_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = lean_st_ref_get(v_a_4025_);
lean_inc_ref(v_rhs_4022_);
v___x_4043_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4042_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v___x_4042_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v_root_4045_; lean_object* v_root_4046_; size_t v___x_4047_; size_t v___x_4048_; uint8_t v___x_4049_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v_root_4045_ = lean_ctor_get(v_a_4041_, 2);
v_root_4046_ = lean_ctor_get(v_a_4044_, 2);
v___x_4047_ = lean_ptr_addr(v_root_4045_);
v___x_4048_ = lean_ptr_addr(v_root_4046_);
v___x_4049_ = lean_usize_dec_eq(v___x_4047_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_object* v_options_4050_; lean_object* v_inheritedTraceOptions_4051_; uint8_t v_hasTrace_4052_; uint8_t v___x_4053_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; uint8_t v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4118_; uint8_t v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; uint8_t v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4163_; lean_object* v___y_4164_; uint8_t v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4179_; uint8_t v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4195_; uint8_t v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; uint8_t v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4211_; uint8_t v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; uint8_t v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; uint8_t v___y_4225_; lean_object* v___y_4227_; uint8_t v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v_size_4231_; uint8_t v_interpreted_4232_; uint8_t v_ctor_4233_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4236_; lean_object* v_size_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; uint8_t v___y_4261_; lean_object* v___y_4272_; lean_object* v___y_4273_; uint8_t v_interpreted_4274_; uint8_t v_valueInconsistency_4275_; uint8_t v_trueEqFalse_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4289_; lean_object* v___y_4290_; uint8_t v_valueInconsistency_4291_; uint8_t v_trueEqFalse_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4319_; uint8_t v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; uint8_t v___y_4359_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; 
v_options_4050_ = lean_ctor_get(v_a_4033_, 2);
v_inheritedTraceOptions_4051_ = lean_ctor_get(v_a_4033_, 13);
v_hasTrace_4052_ = lean_ctor_get_uint8(v_options_4050_, sizeof(void*)*1);
v___x_4053_ = 1;
if (v_hasTrace_4052_ == 0)
{
v___y_4366_ = v_a_4025_;
v___y_4367_ = v_a_4026_;
v___y_4368_ = v_a_4027_;
v___y_4369_ = v_a_4028_;
v___y_4370_ = v_a_4029_;
v___y_4371_ = v_a_4030_;
v___y_4372_ = v_a_4031_;
v___y_4373_ = v_a_4032_;
v___y_4374_ = v_a_4033_;
v___y_4375_ = v_a_4034_;
goto v___jp_4365_;
}
else
{
lean_object* v___x_4401_; lean_object* v_____do__lift_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v___x_4401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4051_, v_options_4050_, v___x_4416_);
if (v___x_4417_ == 0)
{
v___y_4366_ = v_a_4025_;
v___y_4367_ = v_a_4026_;
v___y_4368_ = v_a_4027_;
v___y_4369_ = v_a_4028_;
v___y_4370_ = v_a_4029_;
v___y_4371_ = v_a_4030_;
v___y_4372_ = v_a_4031_;
v___y_4373_ = v_a_4032_;
v___y_4374_ = v_a_4033_;
v___y_4375_ = v_a_4034_;
goto v___jp_4365_;
}
else
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Meta_Grind_updateLastTag(v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_dec_ref_known(v___x_4418_, 1);
if (v_isHEq_4024_ == 0)
{
lean_object* v___x_4419_; 
lean_inc_ref(v_rhs_4022_);
lean_inc_ref(v_lhs_4021_);
v___x_4419_ = l_Lean_Meta_mkEq(v_lhs_4021_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v_____do__lift_4403_ = v_a_4420_;
v___y_4404_ = v_a_4025_;
v___y_4405_ = v_a_4026_;
v___y_4406_ = v_a_4027_;
v___y_4407_ = v_a_4028_;
v___y_4408_ = v_a_4029_;
v___y_4409_ = v_a_4030_;
v___y_4410_ = v_a_4031_;
v___y_4411_ = v_a_4032_;
v___y_4412_ = v_a_4033_;
v___y_4413_ = v_a_4034_;
goto v___jp_4402_;
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4421_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4419_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4419_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
lean_object* v___x_4429_; 
lean_inc_ref(v_rhs_4022_);
lean_inc_ref(v_lhs_4021_);
v___x_4429_ = l_Lean_Meta_mkHEq(v_lhs_4021_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v_____do__lift_4403_ = v_a_4430_;
v___y_4404_ = v_a_4025_;
v___y_4405_ = v_a_4026_;
v___y_4406_ = v_a_4027_;
v___y_4407_ = v_a_4028_;
v___y_4408_ = v_a_4029_;
v___y_4409_ = v_a_4030_;
v___y_4410_ = v_a_4031_;
v___y_4411_ = v_a_4032_;
v___y_4412_ = v_a_4033_;
v___y_4413_ = v_a_4034_;
goto v___jp_4402_;
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4431_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4429_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4429_);
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
}
}
else
{
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4418_;
}
}
v___jp_4402_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = l_Lean_MessageData_ofExpr(v_____do__lift_4403_);
v___x_4415_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4401_, v___x_4414_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_dec_ref_known(v___x_4415_, 1);
v___y_4366_ = v___y_4404_;
v___y_4367_ = v___y_4405_;
v___y_4368_ = v___y_4406_;
v___y_4369_ = v___y_4407_;
v___y_4370_ = v___y_4408_;
v___y_4371_ = v___y_4409_;
v___y_4372_ = v___y_4410_;
v___y_4373_ = v___y_4411_;
v___y_4374_ = v___y_4412_;
v___y_4375_ = v___y_4413_;
goto v___jp_4365_;
}
else
{
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4415_;
}
}
}
v___jp_4054_:
{
lean_object* v_options_4065_; uint8_t v_hasTrace_4066_; 
v_options_4065_ = lean_ctor_get(v___y_4063_, 2);
v_hasTrace_4066_ = lean_ctor_get_uint8(v_options_4065_, sizeof(void*)*1);
if (v_hasTrace_4066_ == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
return v___x_4067_;
}
else
{
lean_object* v_inheritedTraceOptions_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
v_inheritedTraceOptions_4068_ = lean_ctor_get(v___y_4063_, 13);
v___x_4069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4071_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4070_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
return v___x_4072_;
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Meta_Grind_updateLastTag(v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
lean_dec_ref_known(v___x_4073_, 1);
v___x_4074_ = lean_st_ref_get(v___y_4055_);
v___x_4075_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4074_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___x_4074_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v___x_4077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v_a_4076_);
v___x_4079_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4069_, v___x_4078_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v___x_4080_; 
lean_dec_ref_known(v___x_4079_, 1);
v___x_4080_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
return v___x_4080_;
}
else
{
return v___x_4079_;
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_a_4081_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4075_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4075_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
return v___x_4073_;
}
}
}
}
v___jp_4089_:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4093_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; uint8_t v___x_4105_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v___x_4105_ = lean_unbox(v_a_4104_);
lean_dec(v_a_4104_);
if (v___x_4105_ == 0)
{
if (v___y_4090_ == 0)
{
lean_dec_ref(v___y_4092_);
lean_dec_ref(v___y_4091_);
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
v___y_4063_ = v___y_4101_;
v___y_4064_ = v___y_4102_;
goto v___jp_4054_;
}
else
{
lean_object* v_self_4106_; lean_object* v_self_4107_; lean_object* v___x_4108_; 
v_self_4106_ = lean_ctor_get(v___y_4092_, 0);
lean_inc_ref(v_self_4106_);
lean_dec_ref(v___y_4092_);
v_self_4107_ = lean_ctor_get(v___y_4091_, 0);
lean_inc_ref(v_self_4107_);
lean_dec_ref(v___y_4091_);
v___x_4108_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4106_, v_self_4107_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_dec_ref_known(v___x_4108_, 1);
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
v___y_4063_ = v___y_4101_;
v___y_4064_ = v___y_4102_;
goto v___jp_4054_;
}
else
{
return v___x_4108_;
}
}
}
else
{
lean_dec_ref(v___y_4092_);
lean_dec_ref(v___y_4091_);
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
v___y_4063_ = v___y_4101_;
v___y_4064_ = v___y_4102_;
goto v___jp_4054_;
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec_ref(v___y_4092_);
lean_dec_ref(v___y_4091_);
v_a_4109_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4103_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4103_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
v___jp_4117_:
{
if (v___y_4131_ == 0)
{
v___y_4090_ = v___y_4119_;
v___y_4091_ = v___y_4121_;
v___y_4092_ = v___y_4122_;
v___y_4093_ = v___y_4125_;
v___y_4094_ = v___y_4129_;
v___y_4095_ = v___y_4130_;
v___y_4096_ = v___y_4126_;
v___y_4097_ = v___y_4123_;
v___y_4098_ = v___y_4124_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4120_;
goto v___jp_4089_;
}
else
{
lean_object* v_self_4132_; lean_object* v_self_4133_; lean_object* v___x_4134_; 
v_self_4132_ = lean_ctor_get(v___y_4122_, 0);
v_self_4133_ = lean_ctor_get(v___y_4121_, 0);
lean_inc_ref(v_self_4133_);
lean_inc_ref(v_self_4132_);
v___x_4134_ = l_Lean_Meta_Grind_propagateCtor(v_self_4132_, v_self_4133_, v___y_4125_, v___y_4129_, v___y_4130_, v___y_4126_, v___y_4123_, v___y_4124_, v___y_4118_, v___y_4127_, v___y_4128_, v___y_4120_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4090_ = v___y_4119_;
v___y_4091_ = v___y_4121_;
v___y_4092_ = v___y_4122_;
v___y_4093_ = v___y_4125_;
v___y_4094_ = v___y_4129_;
v___y_4095_ = v___y_4130_;
v___y_4096_ = v___y_4126_;
v___y_4097_ = v___y_4123_;
v___y_4098_ = v___y_4124_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4120_;
goto v___jp_4089_;
}
else
{
lean_dec_ref(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v___x_4134_;
}
}
}
v___jp_4135_:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4139_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; uint8_t v___x_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = lean_unbox(v_a_4150_);
lean_dec(v_a_4150_);
if (v___x_4151_ == 0)
{
uint8_t v_ctor_4152_; 
v_ctor_4152_ = lean_ctor_get_uint8(v___y_4138_, sizeof(void*)*12 + 2);
if (v_ctor_4152_ == 0)
{
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4136_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4137_;
v___y_4122_ = v___y_4138_;
v___y_4123_ = v___y_4143_;
v___y_4124_ = v___y_4144_;
v___y_4125_ = v___y_4139_;
v___y_4126_ = v___y_4142_;
v___y_4127_ = v___y_4146_;
v___y_4128_ = v___y_4147_;
v___y_4129_ = v___y_4140_;
v___y_4130_ = v___y_4141_;
v___y_4131_ = v___x_4049_;
goto v___jp_4117_;
}
else
{
uint8_t v_ctor_4153_; 
v_ctor_4153_ = lean_ctor_get_uint8(v___y_4137_, sizeof(void*)*12 + 2);
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4136_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4137_;
v___y_4122_ = v___y_4138_;
v___y_4123_ = v___y_4143_;
v___y_4124_ = v___y_4144_;
v___y_4125_ = v___y_4139_;
v___y_4126_ = v___y_4142_;
v___y_4127_ = v___y_4146_;
v___y_4128_ = v___y_4147_;
v___y_4129_ = v___y_4140_;
v___y_4130_ = v___y_4141_;
v___y_4131_ = v_ctor_4153_;
goto v___jp_4117_;
}
}
else
{
v___y_4090_ = v___y_4136_;
v___y_4091_ = v___y_4137_;
v___y_4092_ = v___y_4138_;
v___y_4093_ = v___y_4139_;
v___y_4094_ = v___y_4140_;
v___y_4095_ = v___y_4141_;
v___y_4096_ = v___y_4142_;
v___y_4097_ = v___y_4143_;
v___y_4098_ = v___y_4144_;
v___y_4099_ = v___y_4145_;
v___y_4100_ = v___y_4146_;
v___y_4101_ = v___y_4147_;
v___y_4102_ = v___y_4148_;
goto v___jp_4089_;
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref(v___y_4138_);
lean_dec_ref(v___y_4137_);
v_a_4154_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4149_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4149_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
v___jp_4162_:
{
if (v___y_4165_ == 0)
{
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4166_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4168_;
v___y_4141_ = v___y_4169_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4172_;
v___y_4145_ = v___y_4173_;
v___y_4146_ = v___y_4174_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___y_4176_;
goto v___jp_4135_;
}
else
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_dec_ref_known(v___x_4177_, 1);
v___y_4136_ = v___y_4163_;
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4166_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4168_;
v___y_4141_ = v___y_4169_;
v___y_4142_ = v___y_4170_;
v___y_4143_ = v___y_4171_;
v___y_4144_ = v___y_4172_;
v___y_4145_ = v___y_4173_;
v___y_4146_ = v___y_4174_;
v___y_4147_ = v___y_4175_;
v___y_4148_ = v___y_4176_;
goto v___jp_4135_;
}
else
{
lean_dec_ref(v___y_4166_);
lean_dec_ref(v___y_4164_);
return v___x_4177_;
}
}
}
v___jp_4178_:
{
lean_object* v___x_4193_; 
lean_inc_ref(v___y_4185_);
lean_inc_ref(v___y_4182_);
v___x_4193_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4023_, v_isHEq_4024_, v_rhs_4022_, v_lhs_4021_, v_a_4044_, v_a_4041_, v___y_4182_, v___y_4185_, v___x_4053_, v___y_4181_, v___y_4179_, v___y_4191_, v___y_4183_, v___y_4186_, v___y_4192_, v___y_4187_, v___y_4190_, v___y_4189_, v___y_4188_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_dec_ref_known(v___x_4193_, 1);
v___y_4163_ = v___y_4180_;
v___y_4164_ = v___y_4182_;
v___y_4165_ = v___y_4184_;
v___y_4166_ = v___y_4185_;
v___y_4167_ = v___y_4181_;
v___y_4168_ = v___y_4179_;
v___y_4169_ = v___y_4191_;
v___y_4170_ = v___y_4183_;
v___y_4171_ = v___y_4186_;
v___y_4172_ = v___y_4192_;
v___y_4173_ = v___y_4187_;
v___y_4174_ = v___y_4190_;
v___y_4175_ = v___y_4189_;
v___y_4176_ = v___y_4188_;
goto v___jp_4162_;
}
else
{
lean_dec_ref(v___y_4185_);
lean_dec_ref(v___y_4182_);
return v___x_4193_;
}
}
v___jp_4194_:
{
lean_object* v___x_4209_; 
lean_inc_ref(v___y_4198_);
lean_inc_ref(v___y_4201_);
v___x_4209_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4023_, v_isHEq_4024_, v_lhs_4021_, v_rhs_4022_, v_a_4041_, v_a_4044_, v___y_4201_, v___y_4198_, v___x_4049_, v___y_4197_, v___y_4195_, v___y_4207_, v___y_4199_, v___y_4202_, v___y_4208_, v___y_4203_, v___y_4206_, v___y_4205_, v___y_4204_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_dec_ref_known(v___x_4209_, 1);
v___y_4163_ = v___y_4196_;
v___y_4164_ = v___y_4198_;
v___y_4165_ = v___y_4200_;
v___y_4166_ = v___y_4201_;
v___y_4167_ = v___y_4197_;
v___y_4168_ = v___y_4195_;
v___y_4169_ = v___y_4207_;
v___y_4170_ = v___y_4199_;
v___y_4171_ = v___y_4202_;
v___y_4172_ = v___y_4208_;
v___y_4173_ = v___y_4203_;
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4205_;
v___y_4176_ = v___y_4204_;
goto v___jp_4162_;
}
else
{
lean_dec_ref(v___y_4201_);
lean_dec_ref(v___y_4198_);
return v___x_4209_;
}
}
v___jp_4210_:
{
if (v___y_4225_ == 0)
{
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
goto v___jp_4194_;
}
else
{
v___y_4179_ = v___y_4211_;
v___y_4180_ = v___y_4212_;
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4215_;
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4217_;
v___y_4186_ = v___y_4218_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4220_;
v___y_4189_ = v___y_4221_;
v___y_4190_ = v___y_4222_;
v___y_4191_ = v___y_4223_;
v___y_4192_ = v___y_4224_;
goto v___jp_4178_;
}
}
v___jp_4226_:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_nat_dec_lt(v_size_4231_, v_size_4237_);
lean_dec(v_size_4237_);
lean_dec(v_size_4231_);
if (v___x_4245_ == 0)
{
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___x_4049_;
goto v___jp_4210_;
}
else
{
if (v_interpreted_4232_ == 0)
{
if (v___x_4245_ == 0)
{
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___x_4049_;
goto v___jp_4210_;
}
else
{
if (v_ctor_4233_ == 0)
{
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___x_4245_;
goto v___jp_4210_;
}
else
{
v___y_4195_ = v___y_4227_;
v___y_4196_ = v___y_4228_;
v___y_4197_ = v___y_4229_;
v___y_4198_ = v___y_4230_;
v___y_4199_ = v___y_4234_;
v___y_4200_ = v___y_4235_;
v___y_4201_ = v___y_4236_;
v___y_4202_ = v___y_4238_;
v___y_4203_ = v___y_4239_;
v___y_4204_ = v___y_4240_;
v___y_4205_ = v___y_4241_;
v___y_4206_ = v___y_4242_;
v___y_4207_ = v___y_4243_;
v___y_4208_ = v___y_4244_;
goto v___jp_4194_;
}
}
}
else
{
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___x_4049_;
goto v___jp_4210_;
}
}
}
v___jp_4246_:
{
if (v___y_4261_ == 0)
{
uint8_t v_ctor_4262_; 
v_ctor_4262_ = lean_ctor_get_uint8(v___y_4253_, sizeof(void*)*12 + 2);
if (v_ctor_4262_ == 0)
{
if (v___x_4049_ == 0)
{
lean_object* v_size_4263_; lean_object* v_size_4264_; uint8_t v_interpreted_4265_; uint8_t v_ctor_4266_; 
v_size_4263_ = lean_ctor_get(v___y_4253_, 6);
lean_inc(v_size_4263_);
v_size_4264_ = lean_ctor_get(v___y_4250_, 6);
lean_inc(v_size_4264_);
v_interpreted_4265_ = lean_ctor_get_uint8(v___y_4250_, sizeof(void*)*12 + 1);
v_ctor_4266_ = lean_ctor_get_uint8(v___y_4250_, sizeof(void*)*12 + 2);
v___y_4227_ = v___y_4247_;
v___y_4228_ = v___y_4248_;
v___y_4229_ = v___y_4249_;
v___y_4230_ = v___y_4250_;
v_size_4231_ = v_size_4264_;
v_interpreted_4232_ = v_interpreted_4265_;
v_ctor_4233_ = v_ctor_4266_;
v___y_4234_ = v___y_4251_;
v___y_4235_ = v___y_4252_;
v___y_4236_ = v___y_4253_;
v_size_4237_ = v_size_4263_;
v___y_4238_ = v___y_4254_;
v___y_4239_ = v___y_4255_;
v___y_4240_ = v___y_4256_;
v___y_4241_ = v___y_4257_;
v___y_4242_ = v___y_4258_;
v___y_4243_ = v___y_4259_;
v___y_4244_ = v___y_4260_;
goto v___jp_4226_;
}
else
{
v___y_4179_ = v___y_4247_;
v___y_4180_ = v___y_4248_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___y_4250_;
v___y_4183_ = v___y_4251_;
v___y_4184_ = v___y_4252_;
v___y_4185_ = v___y_4253_;
v___y_4186_ = v___y_4254_;
v___y_4187_ = v___y_4255_;
v___y_4188_ = v___y_4256_;
v___y_4189_ = v___y_4257_;
v___y_4190_ = v___y_4258_;
v___y_4191_ = v___y_4259_;
v___y_4192_ = v___y_4260_;
goto v___jp_4178_;
}
}
else
{
uint8_t v_ctor_4267_; 
v_ctor_4267_ = lean_ctor_get_uint8(v___y_4250_, sizeof(void*)*12 + 2);
if (v_ctor_4267_ == 0)
{
v___y_4179_ = v___y_4247_;
v___y_4180_ = v___y_4248_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___y_4250_;
v___y_4183_ = v___y_4251_;
v___y_4184_ = v___y_4252_;
v___y_4185_ = v___y_4253_;
v___y_4186_ = v___y_4254_;
v___y_4187_ = v___y_4255_;
v___y_4188_ = v___y_4256_;
v___y_4189_ = v___y_4257_;
v___y_4190_ = v___y_4258_;
v___y_4191_ = v___y_4259_;
v___y_4192_ = v___y_4260_;
goto v___jp_4178_;
}
else
{
lean_object* v_size_4268_; lean_object* v_size_4269_; uint8_t v_interpreted_4270_; 
v_size_4268_ = lean_ctor_get(v___y_4253_, 6);
lean_inc(v_size_4268_);
v_size_4269_ = lean_ctor_get(v___y_4250_, 6);
lean_inc(v_size_4269_);
v_interpreted_4270_ = lean_ctor_get_uint8(v___y_4250_, sizeof(void*)*12 + 1);
v___y_4227_ = v___y_4247_;
v___y_4228_ = v___y_4248_;
v___y_4229_ = v___y_4249_;
v___y_4230_ = v___y_4250_;
v_size_4231_ = v_size_4269_;
v_interpreted_4232_ = v_interpreted_4270_;
v_ctor_4233_ = v_ctor_4267_;
v___y_4234_ = v___y_4251_;
v___y_4235_ = v___y_4252_;
v___y_4236_ = v___y_4253_;
v_size_4237_ = v_size_4268_;
v___y_4238_ = v___y_4254_;
v___y_4239_ = v___y_4255_;
v___y_4240_ = v___y_4256_;
v___y_4241_ = v___y_4257_;
v___y_4242_ = v___y_4258_;
v___y_4243_ = v___y_4259_;
v___y_4244_ = v___y_4260_;
goto v___jp_4226_;
}
}
}
else
{
v___y_4179_ = v___y_4247_;
v___y_4180_ = v___y_4248_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___y_4250_;
v___y_4183_ = v___y_4251_;
v___y_4184_ = v___y_4252_;
v___y_4185_ = v___y_4253_;
v___y_4186_ = v___y_4254_;
v___y_4187_ = v___y_4255_;
v___y_4188_ = v___y_4256_;
v___y_4189_ = v___y_4257_;
v___y_4190_ = v___y_4258_;
v___y_4191_ = v___y_4259_;
v___y_4192_ = v___y_4260_;
goto v___jp_4178_;
}
}
v___jp_4271_:
{
if (v_interpreted_4274_ == 0)
{
v___y_4247_ = v___y_4278_;
v___y_4248_ = v_valueInconsistency_4275_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___y_4272_;
v___y_4251_ = v___y_4280_;
v___y_4252_ = v_trueEqFalse_4276_;
v___y_4253_ = v___y_4273_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4284_;
v___y_4259_ = v___y_4279_;
v___y_4260_ = v___y_4282_;
v___y_4261_ = v___x_4049_;
goto v___jp_4246_;
}
else
{
uint8_t v_interpreted_4287_; 
v_interpreted_4287_ = lean_ctor_get_uint8(v___y_4272_, sizeof(void*)*12 + 1);
if (v_interpreted_4287_ == 0)
{
v___y_4179_ = v___y_4278_;
v___y_4180_ = v_valueInconsistency_4275_;
v___y_4181_ = v___y_4277_;
v___y_4182_ = v___y_4272_;
v___y_4183_ = v___y_4280_;
v___y_4184_ = v_trueEqFalse_4276_;
v___y_4185_ = v___y_4273_;
v___y_4186_ = v___y_4281_;
v___y_4187_ = v___y_4283_;
v___y_4188_ = v___y_4286_;
v___y_4189_ = v___y_4285_;
v___y_4190_ = v___y_4284_;
v___y_4191_ = v___y_4279_;
v___y_4192_ = v___y_4282_;
goto v___jp_4178_;
}
else
{
v___y_4247_ = v___y_4278_;
v___y_4248_ = v_valueInconsistency_4275_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___y_4272_;
v___y_4251_ = v___y_4280_;
v___y_4252_ = v_trueEqFalse_4276_;
v___y_4253_ = v___y_4273_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4286_;
v___y_4257_ = v___y_4285_;
v___y_4258_ = v___y_4284_;
v___y_4259_ = v___y_4279_;
v___y_4260_ = v___y_4282_;
v___y_4261_ = v___x_4049_;
goto v___jp_4246_;
}
}
}
v___jp_4288_:
{
uint8_t v_interpreted_4303_; 
v_interpreted_4303_ = lean_ctor_get_uint8(v___y_4290_, sizeof(void*)*12 + 1);
v___y_4272_ = v___y_4289_;
v___y_4273_ = v___y_4290_;
v_interpreted_4274_ = v_interpreted_4303_;
v_valueInconsistency_4275_ = v_valueInconsistency_4291_;
v_trueEqFalse_4276_ = v_trueEqFalse_4292_;
v___y_4277_ = v___y_4293_;
v___y_4278_ = v___y_4294_;
v___y_4279_ = v___y_4295_;
v___y_4280_ = v___y_4296_;
v___y_4281_ = v___y_4297_;
v___y_4282_ = v___y_4298_;
v___y_4283_ = v___y_4299_;
v___y_4284_ = v___y_4300_;
v___y_4285_ = v___y_4301_;
v___y_4286_ = v___y_4302_;
goto v___jp_4271_;
}
v___jp_4304_:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4308_, v___y_4316_, v___y_4305_, v___y_4311_, v___y_4307_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_dec_ref_known(v___x_4317_, 1);
v___y_4289_ = v___y_4309_;
v___y_4290_ = v___y_4313_;
v_valueInconsistency_4291_ = v___x_4049_;
v_trueEqFalse_4292_ = v___x_4053_;
v___y_4293_ = v___y_4308_;
v___y_4294_ = v___y_4312_;
v___y_4295_ = v___y_4314_;
v___y_4296_ = v___y_4315_;
v___y_4297_ = v___y_4310_;
v___y_4298_ = v___y_4306_;
v___y_4299_ = v___y_4316_;
v___y_4300_ = v___y_4305_;
v___y_4301_ = v___y_4311_;
v___y_4302_ = v___y_4307_;
goto v___jp_4288_;
}
else
{
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4309_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4317_;
}
}
v___jp_4318_:
{
if (v___y_4320_ == 0)
{
lean_object* v_self_4332_; uint8_t v_interpreted_4333_; lean_object* v_self_4334_; lean_object* v___x_4335_; 
v_self_4332_ = lean_ctor_get(v___y_4328_, 0);
v_interpreted_4333_ = lean_ctor_get_uint8(v___y_4328_, sizeof(void*)*12 + 1);
v_self_4334_ = lean_ctor_get(v___y_4324_, 0);
lean_inc_ref(v_self_4334_);
lean_inc_ref(v_self_4332_);
v___x_4335_ = l_Lean_Meta_Grind_hasSameType(v_self_4332_, v_self_4334_, v___y_4331_, v___y_4319_, v___y_4326_, v___y_4322_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; uint8_t v___x_4337_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = lean_unbox(v_a_4336_);
lean_dec(v_a_4336_);
if (v___x_4337_ == 0)
{
v___y_4272_ = v___y_4324_;
v___y_4273_ = v___y_4328_;
v_interpreted_4274_ = v_interpreted_4333_;
v_valueInconsistency_4275_ = v___x_4049_;
v_trueEqFalse_4276_ = v___x_4049_;
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4327_;
v___y_4279_ = v___y_4329_;
v___y_4280_ = v___y_4330_;
v___y_4281_ = v___y_4325_;
v___y_4282_ = v___y_4321_;
v___y_4283_ = v___y_4331_;
v___y_4284_ = v___y_4319_;
v___y_4285_ = v___y_4326_;
v___y_4286_ = v___y_4322_;
goto v___jp_4271_;
}
else
{
v___y_4272_ = v___y_4324_;
v___y_4273_ = v___y_4328_;
v_interpreted_4274_ = v_interpreted_4333_;
v_valueInconsistency_4275_ = v___x_4053_;
v_trueEqFalse_4276_ = v___x_4049_;
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4327_;
v___y_4279_ = v___y_4329_;
v___y_4280_ = v___y_4330_;
v___y_4281_ = v___y_4325_;
v___y_4282_ = v___y_4321_;
v___y_4283_ = v___y_4331_;
v___y_4284_ = v___y_4319_;
v___y_4285_ = v___y_4326_;
v___y_4286_ = v___y_4322_;
goto v___jp_4271_;
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec_ref(v___y_4328_);
lean_dec_ref(v___y_4324_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4338_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4335_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4335_);
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
v___y_4289_ = v___y_4324_;
v___y_4290_ = v___y_4328_;
v_valueInconsistency_4291_ = v___x_4053_;
v_trueEqFalse_4292_ = v___x_4049_;
v___y_4293_ = v___y_4323_;
v___y_4294_ = v___y_4327_;
v___y_4295_ = v___y_4329_;
v___y_4296_ = v___y_4330_;
v___y_4297_ = v___y_4325_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___y_4331_;
v___y_4300_ = v___y_4319_;
v___y_4301_ = v___y_4326_;
v___y_4302_ = v___y_4322_;
goto v___jp_4288_;
}
}
v___jp_4346_:
{
if (v___y_4359_ == 0)
{
v___y_4289_ = v___y_4351_;
v___y_4290_ = v___y_4355_;
v_valueInconsistency_4291_ = v___x_4049_;
v_trueEqFalse_4292_ = v___x_4049_;
v___y_4293_ = v___y_4350_;
v___y_4294_ = v___y_4353_;
v___y_4295_ = v___y_4356_;
v___y_4296_ = v___y_4357_;
v___y_4297_ = v___y_4352_;
v___y_4298_ = v___y_4348_;
v___y_4299_ = v___y_4358_;
v___y_4300_ = v___y_4347_;
v___y_4301_ = v___y_4354_;
v___y_4302_ = v___y_4349_;
goto v___jp_4288_;
}
else
{
uint8_t v___x_4360_; 
lean_inc_ref(v_root_4045_);
v___x_4360_ = l_Lean_Expr_isTrue(v_root_4045_);
if (v___x_4360_ == 0)
{
uint8_t v___x_4361_; 
lean_inc_ref(v_root_4046_);
v___x_4361_ = l_Lean_Expr_isTrue(v_root_4046_);
if (v___x_4361_ == 0)
{
if (v_isHEq_4024_ == 0)
{
uint8_t v_heqProofs_4362_; 
v_heqProofs_4362_ = lean_ctor_get_uint8(v___y_4355_, sizeof(void*)*12 + 4);
if (v_heqProofs_4362_ == 0)
{
uint8_t v_heqProofs_4363_; 
v_heqProofs_4363_ = lean_ctor_get_uint8(v___y_4351_, sizeof(void*)*12 + 4);
if (v_heqProofs_4363_ == 0)
{
uint8_t v_interpreted_4364_; 
v_interpreted_4364_ = lean_ctor_get_uint8(v___y_4355_, sizeof(void*)*12 + 1);
v___y_4272_ = v___y_4351_;
v___y_4273_ = v___y_4355_;
v_interpreted_4274_ = v_interpreted_4364_;
v_valueInconsistency_4275_ = v___x_4053_;
v_trueEqFalse_4276_ = v___x_4049_;
v___y_4277_ = v___y_4350_;
v___y_4278_ = v___y_4353_;
v___y_4279_ = v___y_4356_;
v___y_4280_ = v___y_4357_;
v___y_4281_ = v___y_4352_;
v___y_4282_ = v___y_4348_;
v___y_4283_ = v___y_4358_;
v___y_4284_ = v___y_4347_;
v___y_4285_ = v___y_4354_;
v___y_4286_ = v___y_4349_;
goto v___jp_4271_;
}
else
{
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___x_4361_;
v___y_4321_ = v___y_4348_;
v___y_4322_ = v___y_4349_;
v___y_4323_ = v___y_4350_;
v___y_4324_ = v___y_4351_;
v___y_4325_ = v___y_4352_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4353_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
v___y_4331_ = v___y_4358_;
goto v___jp_4318_;
}
}
else
{
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___x_4361_;
v___y_4321_ = v___y_4348_;
v___y_4322_ = v___y_4349_;
v___y_4323_ = v___y_4350_;
v___y_4324_ = v___y_4351_;
v___y_4325_ = v___y_4352_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4353_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
v___y_4331_ = v___y_4358_;
goto v___jp_4318_;
}
}
else
{
v___y_4319_ = v___y_4347_;
v___y_4320_ = v___x_4361_;
v___y_4321_ = v___y_4348_;
v___y_4322_ = v___y_4349_;
v___y_4323_ = v___y_4350_;
v___y_4324_ = v___y_4351_;
v___y_4325_ = v___y_4352_;
v___y_4326_ = v___y_4354_;
v___y_4327_ = v___y_4353_;
v___y_4328_ = v___y_4355_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4357_;
v___y_4331_ = v___y_4358_;
goto v___jp_4318_;
}
}
else
{
v___y_4305_ = v___y_4347_;
v___y_4306_ = v___y_4348_;
v___y_4307_ = v___y_4349_;
v___y_4308_ = v___y_4350_;
v___y_4309_ = v___y_4351_;
v___y_4310_ = v___y_4352_;
v___y_4311_ = v___y_4354_;
v___y_4312_ = v___y_4353_;
v___y_4313_ = v___y_4355_;
v___y_4314_ = v___y_4356_;
v___y_4315_ = v___y_4357_;
v___y_4316_ = v___y_4358_;
goto v___jp_4304_;
}
}
else
{
v___y_4305_ = v___y_4347_;
v___y_4306_ = v___y_4348_;
v___y_4307_ = v___y_4349_;
v___y_4308_ = v___y_4350_;
v___y_4309_ = v___y_4351_;
v___y_4310_ = v___y_4352_;
v___y_4311_ = v___y_4354_;
v___y_4312_ = v___y_4353_;
v___y_4313_ = v___y_4355_;
v___y_4314_ = v___y_4356_;
v___y_4315_ = v___y_4357_;
v___y_4316_ = v___y_4358_;
goto v___jp_4304_;
}
}
}
v___jp_4365_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_st_ref_get(v___y_4366_);
lean_inc_ref(v_root_4045_);
v___x_4377_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4376_, v_root_4045_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___x_4376_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = lean_st_ref_get(v___y_4366_);
lean_inc_ref(v_root_4046_);
v___x_4380_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4379_, v_root_4046_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___x_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
uint8_t v_interpreted_4381_; 
v_interpreted_4381_ = lean_ctor_get_uint8(v_a_4378_, sizeof(void*)*12 + 1);
if (v_interpreted_4381_ == 0)
{
lean_object* v_a_4382_; 
v_a_4382_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4380_, 1);
v___y_4347_ = v___y_4373_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4375_;
v___y_4350_ = v___y_4366_;
v___y_4351_ = v_a_4382_;
v___y_4352_ = v___y_4370_;
v___y_4353_ = v___y_4367_;
v___y_4354_ = v___y_4374_;
v___y_4355_ = v_a_4378_;
v___y_4356_ = v___y_4368_;
v___y_4357_ = v___y_4369_;
v___y_4358_ = v___y_4372_;
v___y_4359_ = v___x_4049_;
goto v___jp_4346_;
}
else
{
lean_object* v_a_4383_; uint8_t v_interpreted_4384_; 
v_a_4383_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4380_, 1);
v_interpreted_4384_ = lean_ctor_get_uint8(v_a_4383_, sizeof(void*)*12 + 1);
v___y_4347_ = v___y_4373_;
v___y_4348_ = v___y_4371_;
v___y_4349_ = v___y_4375_;
v___y_4350_ = v___y_4366_;
v___y_4351_ = v_a_4383_;
v___y_4352_ = v___y_4370_;
v___y_4353_ = v___y_4367_;
v___y_4354_ = v___y_4374_;
v___y_4355_ = v_a_4378_;
v___y_4356_ = v___y_4368_;
v___y_4357_ = v___y_4369_;
v___y_4358_ = v___y_4372_;
v___y_4359_ = v_interpreted_4384_;
goto v___jp_4346_;
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_a_4378_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4385_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4380_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4380_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4393_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4377_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4377_);
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
}
else
{
lean_object* v_options_4439_; uint8_t v_hasTrace_4440_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
v_options_4439_ = lean_ctor_get(v_a_4033_, 2);
v_hasTrace_4440_ = lean_ctor_get_uint8(v_options_4439_, sizeof(void*)*1);
if (v_hasTrace_4440_ == 0)
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
goto v___jp_4036_;
}
else
{
lean_object* v_inheritedTraceOptions_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v_inheritedTraceOptions_4441_ = lean_ctor_get(v_a_4033_, 13);
v___x_4442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4444_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4441_, v_options_4439_, v___x_4443_);
if (v___x_4444_ == 0)
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
goto v___jp_4036_;
}
else
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_Meta_Grind_updateLastTag(v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v___x_4446_; 
lean_dec_ref_known(v___x_4445_, 1);
v___x_4446_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4021_, v_a_4025_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4448_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___x_4448_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4022_, v_a_4025_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref_known(v___x_4448_, 1);
v___x_4450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4451_, 0, v_a_4447_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v_a_4449_);
v___x_4453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4452_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
v___x_4455_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4442_, v___x_4454_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_dec_ref_known(v___x_4455_, 1);
goto v___jp_4036_;
}
else
{
return v___x_4455_;
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_a_4447_);
v_a_4456_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4448_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4448_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_dec_ref(v_rhs_4022_);
v_a_4464_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4446_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4446_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4445_;
}
}
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4472_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4043_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4043_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4480_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4040_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4040_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
v___jp_4036_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4488_, lean_object* v_rhs_4489_, lean_object* v_proof_4490_, lean_object* v_isHEq_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
uint8_t v_isHEq_boxed_4503_; lean_object* v_res_4504_; 
v_isHEq_boxed_4503_ = lean_unbox(v_isHEq_4491_);
v_res_4504_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4488_, v_rhs_4489_, v_proof_4490_, v_isHEq_boxed_4503_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_a_4493_);
lean_dec(v_a_4492_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4507_){
_start:
{
lean_object* v___x_4509_; lean_object* v_toGoalState_4510_; lean_object* v_mvarId_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4547_; 
v___x_4509_ = lean_st_ref_take(v_a_4507_);
v_toGoalState_4510_ = lean_ctor_get(v___x_4509_, 0);
v_mvarId_4511_ = lean_ctor_get(v___x_4509_, 1);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4513_ = v___x_4509_;
v_isShared_4514_ = v_isSharedCheck_4547_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_mvarId_4511_);
lean_inc(v_toGoalState_4510_);
lean_dec(v___x_4509_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4547_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_nextDeclIdx_4515_; lean_object* v_enodeMap_4516_; lean_object* v_exprs_4517_; lean_object* v_parents_4518_; lean_object* v_congrTable_4519_; lean_object* v_appMap_4520_; lean_object* v_indicesFound_4521_; uint8_t v_inconsistent_4522_; lean_object* v_nextIdx_4523_; lean_object* v_newRawFacts_4524_; lean_object* v_facts_4525_; lean_object* v_extThms_4526_; lean_object* v_ematch_4527_; lean_object* v_inj_4528_; lean_object* v_split_4529_; lean_object* v_clean_4530_; lean_object* v_sstates_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4545_; 
v_nextDeclIdx_4515_ = lean_ctor_get(v_toGoalState_4510_, 0);
v_enodeMap_4516_ = lean_ctor_get(v_toGoalState_4510_, 1);
v_exprs_4517_ = lean_ctor_get(v_toGoalState_4510_, 2);
v_parents_4518_ = lean_ctor_get(v_toGoalState_4510_, 3);
v_congrTable_4519_ = lean_ctor_get(v_toGoalState_4510_, 4);
v_appMap_4520_ = lean_ctor_get(v_toGoalState_4510_, 5);
v_indicesFound_4521_ = lean_ctor_get(v_toGoalState_4510_, 6);
v_inconsistent_4522_ = lean_ctor_get_uint8(v_toGoalState_4510_, sizeof(void*)*17);
v_nextIdx_4523_ = lean_ctor_get(v_toGoalState_4510_, 8);
v_newRawFacts_4524_ = lean_ctor_get(v_toGoalState_4510_, 9);
v_facts_4525_ = lean_ctor_get(v_toGoalState_4510_, 10);
v_extThms_4526_ = lean_ctor_get(v_toGoalState_4510_, 11);
v_ematch_4527_ = lean_ctor_get(v_toGoalState_4510_, 12);
v_inj_4528_ = lean_ctor_get(v_toGoalState_4510_, 13);
v_split_4529_ = lean_ctor_get(v_toGoalState_4510_, 14);
v_clean_4530_ = lean_ctor_get(v_toGoalState_4510_, 15);
v_sstates_4531_ = lean_ctor_get(v_toGoalState_4510_, 16);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_toGoalState_4510_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v_toGoalState_4510_, 7);
lean_dec(v_unused_4546_);
v___x_4533_ = v_toGoalState_4510_;
v_isShared_4534_ = v_isSharedCheck_4545_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_sstates_4531_);
lean_inc(v_clean_4530_);
lean_inc(v_split_4529_);
lean_inc(v_inj_4528_);
lean_inc(v_ematch_4527_);
lean_inc(v_extThms_4526_);
lean_inc(v_facts_4525_);
lean_inc(v_newRawFacts_4524_);
lean_inc(v_nextIdx_4523_);
lean_inc(v_indicesFound_4521_);
lean_inc(v_appMap_4520_);
lean_inc(v_congrTable_4519_);
lean_inc(v_parents_4518_);
lean_inc(v_exprs_4517_);
lean_inc(v_enodeMap_4516_);
lean_inc(v_nextDeclIdx_4515_);
lean_dec(v_toGoalState_4510_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4545_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4537_; 
v___x_4535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 7, v___x_4535_);
v___x_4537_ = v___x_4533_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_nextDeclIdx_4515_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_enodeMap_4516_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v_exprs_4517_);
lean_ctor_set(v_reuseFailAlloc_4544_, 3, v_parents_4518_);
lean_ctor_set(v_reuseFailAlloc_4544_, 4, v_congrTable_4519_);
lean_ctor_set(v_reuseFailAlloc_4544_, 5, v_appMap_4520_);
lean_ctor_set(v_reuseFailAlloc_4544_, 6, v_indicesFound_4521_);
lean_ctor_set(v_reuseFailAlloc_4544_, 7, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4544_, 8, v_nextIdx_4523_);
lean_ctor_set(v_reuseFailAlloc_4544_, 9, v_newRawFacts_4524_);
lean_ctor_set(v_reuseFailAlloc_4544_, 10, v_facts_4525_);
lean_ctor_set(v_reuseFailAlloc_4544_, 11, v_extThms_4526_);
lean_ctor_set(v_reuseFailAlloc_4544_, 12, v_ematch_4527_);
lean_ctor_set(v_reuseFailAlloc_4544_, 13, v_inj_4528_);
lean_ctor_set(v_reuseFailAlloc_4544_, 14, v_split_4529_);
lean_ctor_set(v_reuseFailAlloc_4544_, 15, v_clean_4530_);
lean_ctor_set(v_reuseFailAlloc_4544_, 16, v_sstates_4531_);
lean_ctor_set_uint8(v_reuseFailAlloc_4544_, sizeof(void*)*17, v_inconsistent_4522_);
v___x_4537_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4539_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4537_);
v___x_4539_ = v___x_4513_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4537_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_mvarId_4511_);
v___x_4539_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4540_ = lean_st_ref_set(v_a_4507_, v___x_4539_);
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4548_);
lean_dec(v_a_4548_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4551_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec(v_a_4563_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v_toGoalState_4578_; lean_object* v_newFacts_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; uint8_t v___x_4583_; 
v___x_4577_ = lean_st_ref_get(v_a_4575_);
v_toGoalState_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc_ref(v_toGoalState_4578_);
lean_dec(v___x_4577_);
v_newFacts_4579_ = lean_ctor_get(v_toGoalState_4578_, 7);
lean_inc_ref(v_newFacts_4579_);
lean_dec_ref(v_toGoalState_4578_);
v___x_4580_ = lean_array_get_size(v_newFacts_4579_);
v___x_4581_ = lean_unsigned_to_nat(1u);
v___x_4582_ = lean_nat_sub(v___x_4580_, v___x_4581_);
v___x_4583_ = lean_nat_dec_lt(v___x_4582_, v___x_4580_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
lean_dec(v___x_4582_);
lean_dec_ref(v_newFacts_4579_);
v___x_4584_ = lean_box(0);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
else
{
lean_object* v___x_4586_; lean_object* v_toGoalState_4587_; lean_object* v_mvarId_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4625_; 
v___x_4586_ = lean_st_ref_take(v_a_4575_);
v_toGoalState_4587_ = lean_ctor_get(v___x_4586_, 0);
v_mvarId_4588_ = lean_ctor_get(v___x_4586_, 1);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4590_ = v___x_4586_;
v_isShared_4591_ = v_isSharedCheck_4625_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_mvarId_4588_);
lean_inc(v_toGoalState_4587_);
lean_dec(v___x_4586_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4625_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_nextDeclIdx_4592_; lean_object* v_enodeMap_4593_; lean_object* v_exprs_4594_; lean_object* v_parents_4595_; lean_object* v_congrTable_4596_; lean_object* v_appMap_4597_; lean_object* v_indicesFound_4598_; lean_object* v_newFacts_4599_; uint8_t v_inconsistent_4600_; lean_object* v_nextIdx_4601_; lean_object* v_newRawFacts_4602_; lean_object* v_facts_4603_; lean_object* v_extThms_4604_; lean_object* v_ematch_4605_; lean_object* v_inj_4606_; lean_object* v_split_4607_; lean_object* v_clean_4608_; lean_object* v_sstates_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4624_; 
v_nextDeclIdx_4592_ = lean_ctor_get(v_toGoalState_4587_, 0);
v_enodeMap_4593_ = lean_ctor_get(v_toGoalState_4587_, 1);
v_exprs_4594_ = lean_ctor_get(v_toGoalState_4587_, 2);
v_parents_4595_ = lean_ctor_get(v_toGoalState_4587_, 3);
v_congrTable_4596_ = lean_ctor_get(v_toGoalState_4587_, 4);
v_appMap_4597_ = lean_ctor_get(v_toGoalState_4587_, 5);
v_indicesFound_4598_ = lean_ctor_get(v_toGoalState_4587_, 6);
v_newFacts_4599_ = lean_ctor_get(v_toGoalState_4587_, 7);
v_inconsistent_4600_ = lean_ctor_get_uint8(v_toGoalState_4587_, sizeof(void*)*17);
v_nextIdx_4601_ = lean_ctor_get(v_toGoalState_4587_, 8);
v_newRawFacts_4602_ = lean_ctor_get(v_toGoalState_4587_, 9);
v_facts_4603_ = lean_ctor_get(v_toGoalState_4587_, 10);
v_extThms_4604_ = lean_ctor_get(v_toGoalState_4587_, 11);
v_ematch_4605_ = lean_ctor_get(v_toGoalState_4587_, 12);
v_inj_4606_ = lean_ctor_get(v_toGoalState_4587_, 13);
v_split_4607_ = lean_ctor_get(v_toGoalState_4587_, 14);
v_clean_4608_ = lean_ctor_get(v_toGoalState_4587_, 15);
v_sstates_4609_ = lean_ctor_get(v_toGoalState_4587_, 16);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_toGoalState_4587_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4611_ = v_toGoalState_4587_;
v_isShared_4612_ = v_isSharedCheck_4624_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_sstates_4609_);
lean_inc(v_clean_4608_);
lean_inc(v_split_4607_);
lean_inc(v_inj_4606_);
lean_inc(v_ematch_4605_);
lean_inc(v_extThms_4604_);
lean_inc(v_facts_4603_);
lean_inc(v_newRawFacts_4602_);
lean_inc(v_nextIdx_4601_);
lean_inc(v_newFacts_4599_);
lean_inc(v_indicesFound_4598_);
lean_inc(v_appMap_4597_);
lean_inc(v_congrTable_4596_);
lean_inc(v_parents_4595_);
lean_inc(v_exprs_4594_);
lean_inc(v_enodeMap_4593_);
lean_inc(v_nextDeclIdx_4592_);
lean_dec(v_toGoalState_4587_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4624_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = lean_array_pop(v_newFacts_4599_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 7, v___x_4613_);
v___x_4615_ = v___x_4611_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_nextDeclIdx_4592_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_enodeMap_4593_);
lean_ctor_set(v_reuseFailAlloc_4623_, 2, v_exprs_4594_);
lean_ctor_set(v_reuseFailAlloc_4623_, 3, v_parents_4595_);
lean_ctor_set(v_reuseFailAlloc_4623_, 4, v_congrTable_4596_);
lean_ctor_set(v_reuseFailAlloc_4623_, 5, v_appMap_4597_);
lean_ctor_set(v_reuseFailAlloc_4623_, 6, v_indicesFound_4598_);
lean_ctor_set(v_reuseFailAlloc_4623_, 7, v___x_4613_);
lean_ctor_set(v_reuseFailAlloc_4623_, 8, v_nextIdx_4601_);
lean_ctor_set(v_reuseFailAlloc_4623_, 9, v_newRawFacts_4602_);
lean_ctor_set(v_reuseFailAlloc_4623_, 10, v_facts_4603_);
lean_ctor_set(v_reuseFailAlloc_4623_, 11, v_extThms_4604_);
lean_ctor_set(v_reuseFailAlloc_4623_, 12, v_ematch_4605_);
lean_ctor_set(v_reuseFailAlloc_4623_, 13, v_inj_4606_);
lean_ctor_set(v_reuseFailAlloc_4623_, 14, v_split_4607_);
lean_ctor_set(v_reuseFailAlloc_4623_, 15, v_clean_4608_);
lean_ctor_set(v_reuseFailAlloc_4623_, 16, v_sstates_4609_);
lean_ctor_set_uint8(v_reuseFailAlloc_4623_, sizeof(void*)*17, v_inconsistent_4600_);
v___x_4615_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4617_; 
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4615_);
v___x_4617_ = v___x_4590_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_mvarId_4588_);
v___x_4617_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4618_ = lean_st_ref_set(v_a_4575_, v___x_4617_);
v___x_4619_ = lean_array_fget(v_newFacts_4579_, v___x_4582_);
lean_dec(v___x_4582_);
lean_dec_ref(v_newFacts_4579_);
v___x_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
v___x_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
return v___x_4621_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4626_);
lean_dec(v_a_4626_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4629_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec(v_a_4641_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4653_, lean_object* v_rhs_4654_, lean_object* v_proof_4655_, uint8_t v_isHEq_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4653_, v_rhs_4654_, v_proof_4655_, v_isHEq_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v___x_4669_; 
lean_dec_ref_known(v___x_4668_, 1);
lean_inc(v_a_4666_);
lean_inc_ref(v_a_4665_);
lean_inc(v_a_4664_);
lean_inc_ref(v_a_4663_);
lean_inc(v_a_4662_);
lean_inc_ref(v_a_4661_);
lean_inc(v_a_4660_);
lean_inc_ref(v_a_4659_);
lean_inc(v_a_4658_);
lean_inc(v_a_4657_);
v___x_4669_ = lean_grind_process_new_facts(v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4669_;
}
else
{
return v___x_4668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4670_, lean_object* v_rhs_4671_, lean_object* v_proof_4672_, lean_object* v_isHEq_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
uint8_t v_isHEq_boxed_4685_; lean_object* v_res_4686_; 
v_isHEq_boxed_4685_ = lean_unbox(v_isHEq_4673_);
v_res_4686_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4670_, v_rhs_4671_, v_proof_4672_, v_isHEq_boxed_4685_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
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
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4687_, lean_object* v_rhs_4688_, lean_object* v_proof_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
uint8_t v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = 0;
v___x_4702_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4687_, v_rhs_4688_, v_proof_4689_, v___x_4701_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4703_, lean_object* v_rhs_4704_, lean_object* v_proof_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4703_, v_rhs_4704_, v_proof_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
lean_dec(v_a_4711_);
lean_dec_ref(v_a_4710_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec(v_a_4706_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4718_, lean_object* v_rhs_4719_, lean_object* v_proof_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
uint8_t v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = 1;
v___x_4733_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4718_, v_rhs_4719_, v_proof_4720_, v___x_4732_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4734_, lean_object* v_rhs_4735_, lean_object* v_proof_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4734_, v_rhs_4735_, v_proof_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec(v_a_4746_);
lean_dec_ref(v_a_4745_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
lean_dec(v_a_4738_);
lean_dec(v_a_4737_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v___x_4752_; lean_object* v_toGoalState_4753_; lean_object* v_mvarId_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4790_; 
v___x_4752_ = lean_st_ref_take(v_a_4750_);
v_toGoalState_4753_ = lean_ctor_get(v___x_4752_, 0);
v_mvarId_4754_ = lean_ctor_get(v___x_4752_, 1);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4756_ = v___x_4752_;
v_isShared_4757_ = v_isSharedCheck_4790_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_mvarId_4754_);
lean_inc(v_toGoalState_4753_);
lean_dec(v___x_4752_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4790_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v_nextDeclIdx_4758_; lean_object* v_enodeMap_4759_; lean_object* v_exprs_4760_; lean_object* v_parents_4761_; lean_object* v_congrTable_4762_; lean_object* v_appMap_4763_; lean_object* v_indicesFound_4764_; lean_object* v_newFacts_4765_; uint8_t v_inconsistent_4766_; lean_object* v_nextIdx_4767_; lean_object* v_newRawFacts_4768_; lean_object* v_facts_4769_; lean_object* v_extThms_4770_; lean_object* v_ematch_4771_; lean_object* v_inj_4772_; lean_object* v_split_4773_; lean_object* v_clean_4774_; lean_object* v_sstates_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4789_; 
v_nextDeclIdx_4758_ = lean_ctor_get(v_toGoalState_4753_, 0);
v_enodeMap_4759_ = lean_ctor_get(v_toGoalState_4753_, 1);
v_exprs_4760_ = lean_ctor_get(v_toGoalState_4753_, 2);
v_parents_4761_ = lean_ctor_get(v_toGoalState_4753_, 3);
v_congrTable_4762_ = lean_ctor_get(v_toGoalState_4753_, 4);
v_appMap_4763_ = lean_ctor_get(v_toGoalState_4753_, 5);
v_indicesFound_4764_ = lean_ctor_get(v_toGoalState_4753_, 6);
v_newFacts_4765_ = lean_ctor_get(v_toGoalState_4753_, 7);
v_inconsistent_4766_ = lean_ctor_get_uint8(v_toGoalState_4753_, sizeof(void*)*17);
v_nextIdx_4767_ = lean_ctor_get(v_toGoalState_4753_, 8);
v_newRawFacts_4768_ = lean_ctor_get(v_toGoalState_4753_, 9);
v_facts_4769_ = lean_ctor_get(v_toGoalState_4753_, 10);
v_extThms_4770_ = lean_ctor_get(v_toGoalState_4753_, 11);
v_ematch_4771_ = lean_ctor_get(v_toGoalState_4753_, 12);
v_inj_4772_ = lean_ctor_get(v_toGoalState_4753_, 13);
v_split_4773_ = lean_ctor_get(v_toGoalState_4753_, 14);
v_clean_4774_ = lean_ctor_get(v_toGoalState_4753_, 15);
v_sstates_4775_ = lean_ctor_get(v_toGoalState_4753_, 16);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_toGoalState_4753_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4777_ = v_toGoalState_4753_;
v_isShared_4778_ = v_isSharedCheck_4789_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_sstates_4775_);
lean_inc(v_clean_4774_);
lean_inc(v_split_4773_);
lean_inc(v_inj_4772_);
lean_inc(v_ematch_4771_);
lean_inc(v_extThms_4770_);
lean_inc(v_facts_4769_);
lean_inc(v_newRawFacts_4768_);
lean_inc(v_nextIdx_4767_);
lean_inc(v_newFacts_4765_);
lean_inc(v_indicesFound_4764_);
lean_inc(v_appMap_4763_);
lean_inc(v_congrTable_4762_);
lean_inc(v_parents_4761_);
lean_inc(v_exprs_4760_);
lean_inc(v_enodeMap_4759_);
lean_inc(v_nextDeclIdx_4758_);
lean_dec(v_toGoalState_4753_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4789_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4779_ = l_Lean_PersistentArray_push___redArg(v_facts_4769_, v_fact_4749_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 10, v___x_4779_);
v___x_4781_ = v___x_4777_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_nextDeclIdx_4758_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_enodeMap_4759_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_exprs_4760_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_parents_4761_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_congrTable_4762_);
lean_ctor_set(v_reuseFailAlloc_4788_, 5, v_appMap_4763_);
lean_ctor_set(v_reuseFailAlloc_4788_, 6, v_indicesFound_4764_);
lean_ctor_set(v_reuseFailAlloc_4788_, 7, v_newFacts_4765_);
lean_ctor_set(v_reuseFailAlloc_4788_, 8, v_nextIdx_4767_);
lean_ctor_set(v_reuseFailAlloc_4788_, 9, v_newRawFacts_4768_);
lean_ctor_set(v_reuseFailAlloc_4788_, 10, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4788_, 11, v_extThms_4770_);
lean_ctor_set(v_reuseFailAlloc_4788_, 12, v_ematch_4771_);
lean_ctor_set(v_reuseFailAlloc_4788_, 13, v_inj_4772_);
lean_ctor_set(v_reuseFailAlloc_4788_, 14, v_split_4773_);
lean_ctor_set(v_reuseFailAlloc_4788_, 15, v_clean_4774_);
lean_ctor_set(v_reuseFailAlloc_4788_, 16, v_sstates_4775_);
lean_ctor_set_uint8(v_reuseFailAlloc_4788_, sizeof(void*)*17, v_inconsistent_4766_);
v___x_4781_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4783_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v___x_4781_);
v___x_4783_ = v___x_4756_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v_mvarId_4754_);
v___x_4783_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4784_ = lean_st_ref_set(v_a_4750_, v___x_4783_);
v___x_4785_ = lean_box(0);
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
return v___x_4786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4791_, v_a_4792_);
lean_dec(v_a_4792_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4795_, v_a_4796_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec(v_a_4809_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4821_, lean_object* v_rhs_4822_, lean_object* v_proof_4823_, lean_object* v_generation_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_){
_start:
{
lean_object* v___x_4836_; 
lean_inc_ref(v_rhs_4822_);
lean_inc_ref(v_lhs_4821_);
v___x_4836_ = l_Lean_Meta_mkEq(v_lhs_4821_, v_rhs_4822_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4848_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc_n(v_a_4837_, 2);
lean_dec_ref_known(v___x_4836_, 1);
v___x_4838_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4837_, v_a_4825_);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4848_ == 0)
{
lean_object* v_unused_4849_; 
v_unused_4849_ = lean_ctor_get(v___x_4838_, 0);
lean_dec(v_unused_4849_);
v___x_4840_ = v___x_4838_;
v_isShared_4841_ = v_isSharedCheck_4848_;
goto v_resetjp_4839_;
}
else
{
lean_dec(v___x_4838_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4848_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
lean_ctor_set_tag(v___x_4840_, 1);
lean_ctor_set(v___x_4840_, 0, v_a_4837_);
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4837_);
v___x_4843_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4844_; 
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc_ref(v_a_4831_);
lean_inc(v_a_4830_);
lean_inc_ref(v_a_4829_);
lean_inc(v_a_4828_);
lean_inc_ref(v_a_4827_);
lean_inc(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v___x_4843_);
lean_inc(v_generation_4824_);
lean_inc_ref(v_lhs_4821_);
v___x_4844_ = lean_grind_internalize(v_lhs_4821_, v_generation_4824_, v___x_4843_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v___x_4845_; 
lean_dec_ref_known(v___x_4844_, 1);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc_ref(v_a_4831_);
lean_inc(v_a_4830_);
lean_inc_ref(v_a_4829_);
lean_inc(v_a_4828_);
lean_inc_ref(v_a_4827_);
lean_inc(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_rhs_4822_);
v___x_4845_ = lean_grind_internalize(v_rhs_4822_, v_generation_4824_, v___x_4843_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v___x_4846_; 
lean_dec_ref_known(v___x_4845_, 1);
v___x_4846_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4821_, v_rhs_4822_, v_proof_4823_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
return v___x_4846_;
}
else
{
lean_dec_ref(v_proof_4823_);
lean_dec_ref(v_rhs_4822_);
lean_dec_ref(v_lhs_4821_);
return v___x_4845_;
}
}
else
{
lean_dec_ref(v___x_4843_);
lean_dec(v_generation_4824_);
lean_dec_ref(v_proof_4823_);
lean_dec_ref(v_rhs_4822_);
lean_dec_ref(v_lhs_4821_);
return v___x_4844_;
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec(v_generation_4824_);
lean_dec_ref(v_proof_4823_);
lean_dec_ref(v_rhs_4822_);
lean_dec_ref(v_lhs_4821_);
v_a_4850_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4836_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4836_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4858_, lean_object* v_rhs_4859_, lean_object* v_proof_4860_, lean_object* v_generation_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4858_, v_rhs_4859_, v_proof_4860_, v_generation_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
lean_dec(v_a_4863_);
lean_dec(v_a_4862_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4874_, lean_object* v_generation_4875_, lean_object* v_p_4876_, uint8_t v_isNeg_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_box(0);
lean_inc(v_a_4887_);
lean_inc_ref(v_a_4886_);
lean_inc(v_a_4885_);
lean_inc_ref(v_a_4884_);
lean_inc(v_a_4883_);
lean_inc_ref(v_a_4882_);
lean_inc(v_a_4881_);
lean_inc_ref(v_a_4880_);
lean_inc(v_a_4879_);
lean_inc(v_a_4878_);
lean_inc_ref(v_p_4876_);
v___x_4890_ = lean_grind_internalize(v_p_4876_, v_generation_4875_, v___x_4889_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_dec_ref_known(v___x_4890_, 1);
if (v_isNeg_4877_ == 0)
{
lean_object* v___x_4891_; 
v___x_4891_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4882_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4893_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_a_4892_);
lean_dec_ref_known(v___x_4891_, 1);
v___x_4893_ = l_Lean_Meta_mkEqTrue(v_proof_4874_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4895_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref_known(v___x_4893_, 1);
v___x_4895_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4876_, v_a_4892_, v_a_4894_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
return v___x_4895_;
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_dec(v_a_4892_);
lean_dec_ref(v_p_4876_);
v_a_4896_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4893_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4893_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4911_; 
lean_dec_ref(v_p_4876_);
lean_dec_ref(v_proof_4874_);
v_a_4904_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4906_ = v___x_4891_;
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4891_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4909_; 
if (v_isShared_4907_ == 0)
{
v___x_4909_ = v___x_4906_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
else
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4882_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_Meta_mkEqFalse(v_proof_4874_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4876_, v_a_4913_, v_a_4915_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
return v___x_4916_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec(v_a_4913_);
lean_dec_ref(v_p_4876_);
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
lean_dec_ref(v_p_4876_);
lean_dec_ref(v_proof_4874_);
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
}
else
{
lean_dec_ref(v_p_4876_);
lean_dec_ref(v_proof_4874_);
return v___x_4890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4933_, lean_object* v_generation_4934_, lean_object* v_p_4935_, lean_object* v_isNeg_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
uint8_t v_isNeg_boxed_4948_; lean_object* v_res_4949_; 
v_isNeg_boxed_4948_ = lean_unbox(v_isNeg_4936_);
v_res_4949_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4933_, v_generation_4934_, v_p_4935_, v_isNeg_boxed_4948_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec(v_a_4937_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4950_, lean_object* v_generation_4951_, lean_object* v_p_4952_, lean_object* v_lhs_4953_, lean_object* v_rhs_4954_, uint8_t v_isNeg_4955_, uint8_t v_isHEq_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
if (v_isNeg_4955_ == 0)
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_inc_ref(v_p_4952_);
v___x_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_p_4952_);
lean_inc(v_a_4966_);
lean_inc_ref(v_a_4965_);
lean_inc(v_a_4964_);
lean_inc_ref(v_a_4963_);
lean_inc(v_a_4962_);
lean_inc_ref(v_a_4961_);
lean_inc(v_a_4960_);
lean_inc_ref(v_a_4959_);
lean_inc(v_a_4958_);
lean_inc(v_a_4957_);
lean_inc_ref(v___x_4968_);
lean_inc(v_generation_4951_);
lean_inc_ref(v_lhs_4953_);
v___x_4969_ = lean_grind_internalize(v_lhs_4953_, v_generation_4951_, v___x_4968_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v___x_4970_; 
lean_dec_ref_known(v___x_4969_, 1);
lean_inc(v_a_4966_);
lean_inc_ref(v_a_4965_);
lean_inc(v_a_4964_);
lean_inc_ref(v_a_4963_);
lean_inc(v_a_4962_);
lean_inc_ref(v_a_4961_);
lean_inc(v_a_4960_);
lean_inc_ref(v_a_4959_);
lean_inc(v_a_4958_);
lean_inc(v_a_4957_);
lean_inc_ref(v_rhs_4954_);
v___x_4970_ = lean_grind_internalize(v_rhs_4954_, v_generation_4951_, v___x_4968_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
lean_dec_ref_known(v___x_4970_, 1);
v___x_4971_ = lean_box(0);
v___x_4972_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4952_, v___x_4971_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v___x_4973_; 
lean_dec_ref_known(v___x_4972_, 1);
v___x_4973_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4953_, v_rhs_4954_, v_proof_4950_, v_isHEq_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4973_;
}
else
{
lean_dec_ref(v_rhs_4954_);
lean_dec_ref(v_lhs_4953_);
lean_dec_ref(v_proof_4950_);
return v___x_4972_;
}
}
else
{
lean_dec_ref(v_rhs_4954_);
lean_dec_ref(v_lhs_4953_);
lean_dec_ref(v_p_4952_);
lean_dec_ref(v_proof_4950_);
return v___x_4970_;
}
}
else
{
lean_dec_ref_known(v___x_4968_, 1);
lean_dec_ref(v_rhs_4954_);
lean_dec_ref(v_lhs_4953_);
lean_dec_ref(v_p_4952_);
lean_dec(v_generation_4951_);
lean_dec_ref(v_proof_4950_);
return v___x_4969_;
}
}
else
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_dec_ref(v_rhs_4954_);
lean_dec_ref(v_lhs_4953_);
v___x_4974_ = lean_box(0);
lean_inc(v_a_4966_);
lean_inc_ref(v_a_4965_);
lean_inc(v_a_4964_);
lean_inc_ref(v_a_4963_);
lean_inc(v_a_4962_);
lean_inc_ref(v_a_4961_);
lean_inc(v_a_4960_);
lean_inc_ref(v_a_4959_);
lean_inc(v_a_4958_);
lean_inc(v_a_4957_);
lean_inc_ref(v_p_4952_);
v___x_4975_ = lean_grind_internalize(v_p_4952_, v_generation_4951_, v___x_4974_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v___x_4976_; 
lean_dec_ref_known(v___x_4975_, 1);
v___x_4976_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4961_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___x_4978_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
v___x_4978_ = l_Lean_Meta_mkEqFalse(v_proof_4950_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v___x_4980_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref_known(v___x_4978_, 1);
v___x_4980_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4952_, v_a_4977_, v_a_4979_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4980_;
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec(v_a_4977_);
lean_dec_ref(v_p_4952_);
v_a_4981_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4978_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4978_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec_ref(v_p_4952_);
lean_dec_ref(v_proof_4950_);
v_a_4989_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4976_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4976_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_dec_ref(v_p_4952_);
lean_dec_ref(v_proof_4950_);
return v___x_4975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4997_ = _args[0];
lean_object* v_generation_4998_ = _args[1];
lean_object* v_p_4999_ = _args[2];
lean_object* v_lhs_5000_ = _args[3];
lean_object* v_rhs_5001_ = _args[4];
lean_object* v_isNeg_5002_ = _args[5];
lean_object* v_isHEq_5003_ = _args[6];
lean_object* v_a_5004_ = _args[7];
lean_object* v_a_5005_ = _args[8];
lean_object* v_a_5006_ = _args[9];
lean_object* v_a_5007_ = _args[10];
lean_object* v_a_5008_ = _args[11];
lean_object* v_a_5009_ = _args[12];
lean_object* v_a_5010_ = _args[13];
lean_object* v_a_5011_ = _args[14];
lean_object* v_a_5012_ = _args[15];
lean_object* v_a_5013_ = _args[16];
lean_object* v_a_5014_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_5015_; uint8_t v_isHEq_boxed_5016_; lean_object* v_res_5017_; 
v_isNeg_boxed_5015_ = lean_unbox(v_isNeg_5002_);
v_isHEq_boxed_5016_ = lean_unbox(v_isHEq_5003_);
v_res_5017_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4997_, v_generation_4998_, v_p_4999_, v_lhs_5000_, v_rhs_5001_, v_isNeg_boxed_5015_, v_isHEq_boxed_5016_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec(v_a_5004_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_5021_, lean_object* v_generation_5022_, lean_object* v_p_5023_, uint8_t v_isNeg_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___x_5036_; 
lean_inc_ref(v_p_5023_);
v___x_5036_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_5023_, v_a_5032_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = l_Lean_Expr_cleanupAnnotations(v_a_5037_);
v___x_5039_ = l_Lean_Expr_isApp(v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; 
lean_dec_ref(v___x_5038_);
v___x_5040_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5040_;
}
else
{
lean_object* v_arg_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; 
v_arg_5041_ = lean_ctor_get(v___x_5038_, 1);
lean_inc_ref(v_arg_5041_);
v___x_5042_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5038_);
v___x_5043_ = l_Lean_Expr_isApp(v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v___x_5044_; 
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_arg_5041_);
v___x_5044_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5044_;
}
else
{
lean_object* v_arg_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v_arg_5045_ = lean_ctor_get(v___x_5042_, 1);
lean_inc_ref(v_arg_5045_);
v___x_5046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5042_);
v___x_5047_ = l_Lean_Expr_isApp(v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; 
lean_dec_ref(v___x_5046_);
lean_dec_ref(v_arg_5045_);
lean_dec_ref(v_arg_5041_);
v___x_5048_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5048_;
}
else
{
lean_object* v_arg_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v_arg_5049_ = lean_ctor_get(v___x_5046_, 1);
lean_inc_ref(v_arg_5049_);
v___x_5050_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5046_);
v___x_5051_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5052_ = l_Lean_Expr_isConstOf(v___x_5050_, v___x_5051_);
if (v___x_5052_ == 0)
{
uint8_t v___x_5053_; 
lean_dec_ref(v_arg_5045_);
v___x_5053_ = l_Lean_Expr_isApp(v___x_5050_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
lean_dec_ref(v___x_5050_);
lean_dec_ref(v_arg_5049_);
lean_dec_ref(v_arg_5041_);
v___x_5054_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5054_;
}
else
{
lean_object* v___x_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v___x_5055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5050_);
v___x_5056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5057_ = l_Lean_Expr_isConstOf(v___x_5055_, v___x_5056_);
lean_dec_ref(v___x_5055_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_dec_ref(v_arg_5049_);
lean_dec_ref(v_arg_5041_);
v___x_5058_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5058_;
}
else
{
lean_object* v___x_5059_; 
v___x_5059_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5021_, v_generation_5022_, v_p_5023_, v_arg_5049_, v_arg_5041_, v_isNeg_5024_, v___x_5057_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5059_;
}
}
}
else
{
uint8_t v___x_5060_; 
lean_dec_ref(v___x_5050_);
v___x_5060_ = l_Lean_Expr_isProp(v_arg_5049_);
lean_dec_ref(v_arg_5049_);
if (v___x_5060_ == 0)
{
lean_object* v___x_5061_; 
v___x_5061_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5021_, v_generation_5022_, v_p_5023_, v_arg_5045_, v_arg_5041_, v_isNeg_5024_, v___x_5060_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5061_;
}
else
{
lean_object* v___x_5062_; 
lean_dec_ref(v_arg_5045_);
lean_dec_ref(v_arg_5041_);
v___x_5062_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5021_, v_generation_5022_, v_p_5023_, v_isNeg_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5062_;
}
}
}
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec_ref(v_p_5023_);
lean_dec(v_generation_5022_);
lean_dec_ref(v_proof_5021_);
v_a_5063_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_5036_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5036_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5071_, lean_object* v_generation_5072_, lean_object* v_p_5073_, lean_object* v_isNeg_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
uint8_t v_isNeg_boxed_5086_; lean_object* v_res_5087_; 
v_isNeg_boxed_5086_ = lean_unbox(v_isNeg_5074_);
v_res_5087_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5071_, v_generation_5072_, v_p_5073_, v_isNeg_boxed_5086_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec(v_a_5075_);
return v_res_5087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5096_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5097_ = l_Lean_Name_append(v___x_5096_, v___x_5095_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5098_, lean_object* v_proof_5099_, lean_object* v_generation_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___y_5122_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___y_5128_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v___y_5135_; lean_object* v___x_5143_; lean_object* v_options_5144_; uint8_t v_hasTrace_5145_; 
lean_inc_ref(v_fact_5098_);
v___x_5143_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5098_, v_a_5101_);
lean_dec_ref(v___x_5143_);
v_options_5144_ = lean_ctor_get(v_a_5109_, 2);
v_hasTrace_5145_ = lean_ctor_get_uint8(v_options_5144_, sizeof(void*)*1);
if (v_hasTrace_5145_ == 0)
{
v___y_5126_ = v_a_5101_;
v___y_5127_ = v_a_5102_;
v___y_5128_ = v_a_5103_;
v___y_5129_ = v_a_5104_;
v___y_5130_ = v_a_5105_;
v___y_5131_ = v_a_5106_;
v___y_5132_ = v_a_5107_;
v___y_5133_ = v_a_5108_;
v___y_5134_ = v_a_5109_;
v___y_5135_ = v_a_5110_;
goto v___jp_5125_;
}
else
{
lean_object* v_inheritedTraceOptions_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; 
v_inheritedTraceOptions_5146_ = lean_ctor_get(v_a_5109_, 13);
v___x_5147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5146_, v_options_5144_, v___x_5148_);
if (v___x_5149_ == 0)
{
v___y_5126_ = v_a_5101_;
v___y_5127_ = v_a_5102_;
v___y_5128_ = v_a_5103_;
v___y_5129_ = v_a_5104_;
v___y_5130_ = v_a_5105_;
v___y_5131_ = v_a_5106_;
v___y_5132_ = v_a_5107_;
v___y_5133_ = v_a_5108_;
v___y_5134_ = v_a_5109_;
v___y_5135_ = v_a_5110_;
goto v___jp_5125_;
}
else
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Lean_Meta_Grind_updateLastTag(v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec_ref_known(v___x_5150_, 1);
lean_inc_ref(v_fact_5098_);
v___x_5151_ = l_Lean_MessageData_ofExpr(v_fact_5098_);
v___x_5152_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5147_, v___x_5151_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_dec_ref_known(v___x_5152_, 1);
v___y_5126_ = v_a_5101_;
v___y_5127_ = v_a_5102_;
v___y_5128_ = v_a_5103_;
v___y_5129_ = v_a_5104_;
v___y_5130_ = v_a_5105_;
v___y_5131_ = v_a_5106_;
v___y_5132_ = v_a_5107_;
v___y_5133_ = v_a_5108_;
v___y_5134_ = v_a_5109_;
v___y_5135_ = v_a_5110_;
goto v___jp_5125_;
}
else
{
lean_dec(v_generation_5100_);
lean_dec_ref(v_proof_5099_);
lean_dec_ref(v_fact_5098_);
return v___x_5152_;
}
}
else
{
lean_dec(v_generation_5100_);
lean_dec_ref(v_proof_5099_);
lean_dec_ref(v_fact_5098_);
return v___x_5150_;
}
}
}
v___jp_5112_:
{
uint8_t v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = 0;
v___x_5124_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5099_, v_generation_5100_, v_fact_5098_, v___x_5123_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
return v___x_5124_;
}
v___jp_5125_:
{
lean_object* v___x_5136_; uint8_t v___x_5137_; 
lean_inc_ref(v_fact_5098_);
v___x_5136_ = l_Lean_Expr_cleanupAnnotations(v_fact_5098_);
v___x_5137_ = l_Lean_Expr_isApp(v___x_5136_);
if (v___x_5137_ == 0)
{
lean_dec_ref(v___x_5136_);
v___y_5113_ = v___y_5126_;
v___y_5114_ = v___y_5127_;
v___y_5115_ = v___y_5128_;
v___y_5116_ = v___y_5129_;
v___y_5117_ = v___y_5130_;
v___y_5118_ = v___y_5131_;
v___y_5119_ = v___y_5132_;
v___y_5120_ = v___y_5133_;
v___y_5121_ = v___y_5134_;
v___y_5122_ = v___y_5135_;
goto v___jp_5112_;
}
else
{
lean_object* v_arg_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
v_arg_5138_ = lean_ctor_get(v___x_5136_, 1);
lean_inc_ref(v_arg_5138_);
v___x_5139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5136_);
v___x_5140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5141_ = l_Lean_Expr_isConstOf(v___x_5139_, v___x_5140_);
lean_dec_ref(v___x_5139_);
if (v___x_5141_ == 0)
{
lean_dec_ref(v_arg_5138_);
v___y_5113_ = v___y_5126_;
v___y_5114_ = v___y_5127_;
v___y_5115_ = v___y_5128_;
v___y_5116_ = v___y_5129_;
v___y_5117_ = v___y_5130_;
v___y_5118_ = v___y_5131_;
v___y_5119_ = v___y_5132_;
v___y_5120_ = v___y_5133_;
v___y_5121_ = v___y_5134_;
v___y_5122_ = v___y_5135_;
goto v___jp_5112_;
}
else
{
lean_object* v___x_5142_; 
lean_dec_ref(v_fact_5098_);
v___x_5142_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5099_, v_generation_5100_, v_arg_5138_, v___x_5141_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
return v___x_5142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5153_, lean_object* v_proof_5154_, lean_object* v_generation_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5153_, v_proof_5154_, v_generation_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec(v_a_5161_);
lean_dec_ref(v_a_5160_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
lean_dec(v_a_5157_);
lean_dec(v_a_5156_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5171_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; uint8_t v___x_5184_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref_known(v___x_5182_, 1);
v___x_5184_ = lean_unbox(v_a_5183_);
lean_dec(v_a_5183_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5186_ = l_Lean_Core_checkSystem(v___x_5185_, v___y_5179_, v___y_5180_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref_known(v___x_5186_, 1);
v___x_5187_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5171_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5224_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5190_ = v___x_5187_;
v_isShared_5191_ = v_isSharedCheck_5224_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5187_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5224_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
if (lean_obj_tag(v_a_5188_) == 1)
{
lean_object* v_val_5192_; 
lean_del_object(v___x_5190_);
v_val_5192_ = lean_ctor_get(v_a_5188_, 0);
lean_inc(v_val_5192_);
lean_dec_ref_known(v_a_5188_, 1);
if (lean_obj_tag(v_val_5192_) == 0)
{
lean_object* v_lhs_5193_; lean_object* v_rhs_5194_; lean_object* v_proof_5195_; uint8_t v_isHEq_5196_; lean_object* v___x_5197_; 
v_lhs_5193_ = lean_ctor_get(v_val_5192_, 0);
lean_inc_ref(v_lhs_5193_);
v_rhs_5194_ = lean_ctor_get(v_val_5192_, 1);
lean_inc_ref(v_rhs_5194_);
v_proof_5195_ = lean_ctor_get(v_val_5192_, 2);
lean_inc_ref(v_proof_5195_);
v_isHEq_5196_ = lean_ctor_get_uint8(v_val_5192_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5192_, 3);
v___x_5197_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5193_, v_rhs_5194_, v_proof_5195_, v_isHEq_5196_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_dec_ref_known(v___x_5197_, 1);
goto _start;
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
v_a_5199_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5197_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5197_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
else
{
lean_object* v_prop_5207_; lean_object* v_proof_5208_; lean_object* v_generation_5209_; lean_object* v___x_5210_; 
v_prop_5207_ = lean_ctor_get(v_val_5192_, 0);
lean_inc_ref(v_prop_5207_);
v_proof_5208_ = lean_ctor_get(v_val_5192_, 1);
lean_inc_ref(v_proof_5208_);
v_generation_5209_ = lean_ctor_get(v_val_5192_, 2);
lean_inc(v_generation_5209_);
lean_dec_ref_known(v_val_5192_, 3);
v___x_5210_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5207_, v_proof_5208_, v_generation_5209_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_dec_ref_known(v___x_5210_, 1);
goto _start;
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
v_a_5212_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5210_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5210_);
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
else
{
lean_object* v___x_5220_; lean_object* v___x_5222_; 
lean_dec(v_a_5188_);
v___x_5220_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 0, v___x_5220_);
v___x_5222_ = v___x_5190_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5220_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
v_a_5225_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5187_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5187_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
v_a_5233_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5186_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5186_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
else
{
lean_object* v___x_5241_; 
v___x_5241_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5171_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5249_; 
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5249_ == 0)
{
lean_object* v_unused_5250_; 
v_unused_5250_ = lean_ctor_get(v___x_5241_, 0);
lean_dec(v_unused_5250_);
v___x_5243_ = v___x_5241_;
v_isShared_5244_ = v_isSharedCheck_5249_;
goto v_resetjp_5242_;
}
else
{
lean_dec(v___x_5241_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5249_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5245_; lean_object* v___x_5247_; 
v___x_5245_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5245_);
v___x_5247_ = v___x_5243_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5245_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
v_a_5251_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5241_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5241_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5259_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5182_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5182_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec(v___y_5267_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec(v_a_5279_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5304_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5304_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5304_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v_fst_5295_; 
v_fst_5295_ = lean_ctor_get(v_a_5291_, 0);
lean_inc(v_fst_5295_);
lean_dec(v_a_5291_);
if (lean_obj_tag(v_fst_5295_) == 0)
{
lean_object* v___x_5296_; lean_object* v___x_5298_; 
v___x_5296_ = lean_box(0);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v___x_5296_);
v___x_5298_ = v___x_5293_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v___x_5296_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
else
{
lean_object* v_val_5300_; lean_object* v___x_5302_; 
v_val_5300_ = lean_ctor_get(v_fst_5295_, 0);
lean_inc(v_val_5300_);
lean_dec_ref_known(v_fst_5295_, 1);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v_val_5300_);
v___x_5302_ = v___x_5293_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_val_5300_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
v_a_5305_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5290_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5290_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = lean_grind_process_new_facts(v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5325_, lean_object* v_a_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5339_, lean_object* v_a_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5339_, v_a_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v_a_5340_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5353_, lean_object* v_proof_5354_, lean_object* v_generation_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
uint8_t v___x_5367_; 
lean_inc_ref(v_fact_5353_);
v___x_5367_ = l_Lean_Expr_isTrue(v_fact_5353_);
if (v___x_5367_ == 0)
{
lean_object* v___x_5368_; 
v___x_5368_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5356_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5380_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5371_ = v___x_5368_;
v_isShared_5372_ = v_isSharedCheck_5380_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5368_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5380_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
uint8_t v___x_5373_; 
v___x_5373_ = lean_unbox(v_a_5369_);
lean_dec(v_a_5369_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
lean_del_object(v___x_5371_);
v___x_5374_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5356_);
lean_dec_ref(v___x_5374_);
v___x_5375_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5353_, v_proof_5354_, v_generation_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_);
return v___x_5375_;
}
else
{
lean_object* v___x_5376_; lean_object* v___x_5378_; 
lean_dec(v_generation_5355_);
lean_dec_ref(v_proof_5354_);
lean_dec_ref(v_fact_5353_);
v___x_5376_ = lean_box(0);
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 0, v___x_5376_);
v___x_5378_ = v___x_5371_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5388_; 
lean_dec(v_generation_5355_);
lean_dec_ref(v_proof_5354_);
lean_dec_ref(v_fact_5353_);
v_a_5381_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5368_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5368_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5386_; 
if (v_isShared_5384_ == 0)
{
v___x_5386_ = v___x_5383_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_dec(v_generation_5355_);
lean_dec_ref(v_proof_5354_);
lean_dec_ref(v_fact_5353_);
v___x_5389_ = lean_box(0);
v___x_5390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5389_);
return v___x_5390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5391_, lean_object* v_proof_5392_, lean_object* v_generation_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lean_Meta_Grind_add(v_fact_5391_, v_proof_5392_, v_generation_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec(v_a_5394_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5406_, lean_object* v_generation_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v___x_5419_; 
lean_inc(v_fvarId_5406_);
v___x_5419_ = l_Lean_FVarId_getType___redArg(v_fvarId_5406_, v_a_5414_, v_a_5416_, v_a_5417_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
v___x_5421_ = l_Lean_mkFVar(v_fvarId_5406_);
v___x_5422_ = l_Lean_Meta_Grind_add(v_a_5420_, v___x_5421_, v_generation_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
return v___x_5422_;
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
lean_dec(v_generation_5407_);
lean_dec(v_fvarId_5406_);
v_a_5423_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5419_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5419_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5431_, lean_object* v_generation_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5431_, v_generation_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec_ref(v_a_5439_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec(v_a_5433_);
return v_res_5444_;
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
