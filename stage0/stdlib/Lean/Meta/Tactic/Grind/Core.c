// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Core
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Inv import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.Ctor import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.Beta import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Internalize
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2;
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getFalseExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1;
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__1;
lean_object* l_Lean_Meta_Grind_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetParentsOf___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__4;
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Meta_Grind_instHashableCongrKey___private__1(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1;
extern lean_object* l_Lean_eagerReflBoolFalse;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1;
lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Array_back_x3f___redArg(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1;
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5;
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsInconsistent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_copyParentsTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7;
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_PendingSolverPropagations_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isCongrRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Meta_Grind_instBEqCongrKey___private__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___boxed(lean_object**);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_st_ref_get(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_Grind_Goal_getENode(x_9, x_1, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 3);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_11, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 5);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
x_19 = lean_ctor_get(x_11, 6);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 1);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 2);
x_22 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 3);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*11 + 4);
x_24 = lean_ctor_get(x_11, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_11, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 10);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 lean_ctor_release(x_11, 7);
 lean_ctor_release(x_11, 8);
 lean_ctor_release(x_11, 9);
 lean_ctor_release(x_11, 10);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_17);
x_29 = x_5;
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_35 = x_16;
} else {
 lean_dec_ref(x_16);
 x_35 = lean_box(0);
}
if (x_18 == 0)
{
uint8_t x_40; 
x_40 = 1;
x_36 = x_40;
goto block_39;
}
else
{
uint8_t x_41; 
x_41 = 0;
x_36 = x_41;
goto block_39;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_1);
x_38 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_34, x_36, x_37, x_17, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_29 = x_5;
x_30 = lean_box(0);
goto block_33;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_38;
}
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 11, 5);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_14);
lean_ctor_set(x_31, 3, x_15);
lean_ctor_set(x_31, 4, x_3);
lean_ctor_set(x_31, 5, x_4);
lean_ctor_set(x_31, 6, x_19);
lean_ctor_set(x_31, 7, x_24);
lean_ctor_set(x_31, 8, x_25);
lean_ctor_set(x_31, 9, x_26);
lean_ctor_set(x_31, 10, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*11, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 2, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 3, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*11 + 4, x_23);
x_32 = l_Lean_Meta_Grind_setENode___redArg(x_1, x_31, x_29);
return x_32;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(0);
x_8 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(x_1, x_6, x_7, x_7, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_1, x_2, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isApp(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isArrow(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_3, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_12);
if (x_13 == 0)
{
lean_dec(x_10);
return x_2;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_5);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = lean_array_set(x_5, x_10, x_6);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_array_set(x_5, x_10, x_6);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
case 1:
{
uint8_t x_19; 
lean_inc_ref(x_5);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_array_set(x_5, x_10, x_6);
x_24 = lean_usize_shift_right(x_3, x_7);
x_25 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_22, x_24, x_4);
lean_inc_ref(x_25);
x_26 = l_Lean_PersistentHashMap_isUnaryNode___redArg(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_ctor_set(x_11, 0, x_25);
x_27 = lean_array_set(x_23, x_10, x_11);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec_ref(x_25);
lean_free_object(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_array_set(x_23, x_10, x_28);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_set(x_23, x_10, x_33);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_array_set(x_5, x_10, x_6);
x_37 = lean_usize_shift_right(x_3, x_7);
x_38 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_35, x_37, x_4);
lean_inc_ref(x_38);
x_39 = l_Lean_PersistentHashMap_isUnaryNode___redArg(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_array_set(x_36, x_10, x_40);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec_ref(x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_array_set(x_36, x_10, x_46);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_49 = x_11;
} else {
 lean_dec_ref(x_11);
 x_49 = lean_box(0);
}
x_50 = lean_array_set(x_5, x_10, x_6);
x_51 = lean_usize_shift_right(x_3, x_7);
x_52 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_48, x_51, x_4);
lean_inc_ref(x_52);
x_53 = l_Lean_PersistentHashMap_isUnaryNode___redArg(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_array_set(x_50, x_10, x_54);
lean_dec(x_10);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_52);
lean_dec(x_49);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec_ref(x_53);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_array_set(x_50, x_10, x_61);
lean_dec(x_10);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
default: 
{
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_2;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0(x_1, x_65, x_4);
if (lean_obj_tag(x_67) == 0)
{
return x_2;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc(x_68);
x_69 = l_Array_eraseIdx___redArg(x_65, x_68);
x_70 = l_Array_eraseIdx___redArg(x_66, x_68);
lean_ctor_set(x_2, 1, x_70);
lean_ctor_set(x_2, 0, x_69);
return x_2;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_2);
x_73 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0(x_1, x_71, x_4);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec_ref(x_73);
lean_inc(x_75);
x_76 = l_Array_eraseIdx___redArg(x_71, x_75);
x_77 = l_Array_eraseIdx___redArg(x_72, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_4 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parent", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2;
x_2 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1;
x_3 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remove: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_49; lean_object* x_50; uint8_t x_62; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_16 = x_2;
} else {
 lean_dec_ref(x_2);
 x_16 = lean_box(0);
}
x_62 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_14);
if (x_62 == 0)
{
x_49 = x_62;
x_50 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_63; 
lean_inc(x_14);
x_63 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_14, x_4, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
x_49 = x_65;
x_50 = lean_box(0);
goto block_61;
}
else
{
uint8_t x_66; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
block_48:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_take(x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 2);
x_22 = lean_ctor_get(x_19, 5);
lean_inc_ref(x_21);
x_23 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_21, x_22, x_14);
lean_ctor_set(x_19, 5, x_23);
x_24 = lean_st_ref_set(x_17, x_19);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
x_28 = lean_ctor_get(x_19, 2);
x_29 = lean_ctor_get(x_19, 3);
x_30 = lean_ctor_get(x_19, 4);
x_31 = lean_ctor_get(x_19, 5);
x_32 = lean_ctor_get(x_19, 6);
x_33 = lean_ctor_get(x_19, 7);
x_34 = lean_ctor_get_uint8(x_19, sizeof(void*)*17);
x_35 = lean_ctor_get(x_19, 8);
x_36 = lean_ctor_get(x_19, 9);
x_37 = lean_ctor_get(x_19, 10);
x_38 = lean_ctor_get(x_19, 11);
x_39 = lean_ctor_get(x_19, 12);
x_40 = lean_ctor_get(x_19, 13);
x_41 = lean_ctor_get(x_19, 14);
x_42 = lean_ctor_get(x_19, 15);
x_43 = lean_ctor_get(x_19, 16);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
lean_inc_ref(x_28);
x_44 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_28, x_31, x_14);
x_45 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_28);
lean_ctor_set(x_45, 3, x_29);
lean_ctor_set(x_45, 4, x_30);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_32);
lean_ctor_set(x_45, 7, x_33);
lean_ctor_set(x_45, 8, x_35);
lean_ctor_set(x_45, 9, x_36);
lean_ctor_set(x_45, 10, x_37);
lean_ctor_set(x_45, 11, x_38);
lean_ctor_set(x_45, 12, x_39);
lean_ctor_set(x_45, 13, x_40);
lean_ctor_set(x_45, 14, x_41);
lean_ctor_set(x_45, 15, x_42);
lean_ctor_set(x_45, 16, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*17, x_34);
x_46 = lean_st_ref_set(x_17, x_45);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
block_61:
{
if (x_49 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3;
x_53 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_52, x_10);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_dec(x_16);
x_17 = x_4;
x_18 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_56);
x_57 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5;
lean_inc(x_14);
x_58 = l_Lean_MessageData_ofExpr(x_14);
if (lean_is_scalar(x_16)) {
 x_59 = lean_alloc_ctor(7, 2, 0);
} else {
 x_59 = x_16;
 lean_ctor_set_tag(x_59, 7);
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_52, x_59, x_8, x_9, x_10, x_11);
lean_dec_ref(x_60);
x_17 = x_4;
x_18 = lean_box(0);
goto block_48;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_56;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_50; lean_object* x_51; uint8_t x_63; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_17 = x_3;
} else {
 lean_dec_ref(x_3);
 x_17 = lean_box(0);
}
x_63 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_15);
if (x_63 == 0)
{
x_50 = x_63;
x_51 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_64; 
lean_inc(x_15);
x_64 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_15, x_5, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
x_50 = x_66;
x_51 = lean_box(0);
goto block_62;
}
else
{
uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
block_49:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_take(x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 2);
x_23 = lean_ctor_get(x_20, 5);
lean_inc_ref(x_22);
x_24 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_22, x_23, x_15);
lean_ctor_set(x_20, 5, x_24);
x_25 = lean_st_ref_set(x_18, x_20);
x_26 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(x_1, x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
x_29 = lean_ctor_get(x_20, 2);
x_30 = lean_ctor_get(x_20, 3);
x_31 = lean_ctor_get(x_20, 4);
x_32 = lean_ctor_get(x_20, 5);
x_33 = lean_ctor_get(x_20, 6);
x_34 = lean_ctor_get(x_20, 7);
x_35 = lean_ctor_get_uint8(x_20, sizeof(void*)*17);
x_36 = lean_ctor_get(x_20, 8);
x_37 = lean_ctor_get(x_20, 9);
x_38 = lean_ctor_get(x_20, 10);
x_39 = lean_ctor_get(x_20, 11);
x_40 = lean_ctor_get(x_20, 12);
x_41 = lean_ctor_get(x_20, 13);
x_42 = lean_ctor_get(x_20, 14);
x_43 = lean_ctor_get(x_20, 15);
x_44 = lean_ctor_get(x_20, 16);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
lean_inc_ref(x_29);
x_45 = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(x_29, x_32, x_15);
x_46 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_28);
lean_ctor_set(x_46, 2, x_29);
lean_ctor_set(x_46, 3, x_30);
lean_ctor_set(x_46, 4, x_31);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_46, 6, x_33);
lean_ctor_set(x_46, 7, x_34);
lean_ctor_set(x_46, 8, x_36);
lean_ctor_set(x_46, 9, x_37);
lean_ctor_set(x_46, 10, x_38);
lean_ctor_set(x_46, 11, x_39);
lean_ctor_set(x_46, 12, x_40);
lean_ctor_set(x_46, 13, x_41);
lean_ctor_set(x_46, 14, x_42);
lean_ctor_set(x_46, 15, x_43);
lean_ctor_set(x_46, 16, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*17, x_35);
x_47 = lean_st_ref_set(x_18, x_46);
x_48 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(x_1, x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_48;
}
}
block_62:
{
if (x_50 == 0)
{
lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_15);
x_52 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(x_1, x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3;
x_54 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_53, x_11);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_dec(x_17);
x_18 = x_5;
x_19 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_57);
x_58 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5;
lean_inc(x_15);
x_59 = l_Lean_MessageData_ofExpr(x_15);
if (lean_is_scalar(x_17)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_17;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_53, x_60, x_9, x_10, x_11, x_12);
lean_dec_ref(x_61);
x_18 = x_5;
x_19 = lean_box(0);
goto block_49;
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_Grind_ParentSet_elems(x_12);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg(x_14, x_13, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reinsert: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; lean_object* x_30; uint8_t x_42; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_16 = x_2;
} else {
 lean_dec_ref(x_2);
 x_16 = lean_box(0);
}
x_42 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_14);
if (x_42 == 0)
{
x_29 = x_42;
x_30 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_43; 
lean_inc(x_14);
x_43 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_14, x_4, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
x_29 = x_45;
x_30 = lean_box(0);
goto block_41;
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
block_28:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_addCongrTable(x_14, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_26;
}
}
block_41:
{
if (x_29 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3;
x_33 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_32, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_36);
x_37 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1;
lean_inc(x_14);
x_38 = l_Lean_MessageData_ofExpr(x_14);
if (lean_is_scalar(x_16)) {
 x_39 = lean_alloc_ctor(7, 2, 0);
} else {
 x_39 = x_16;
 lean_ctor_set_tag(x_39, 7);
}
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_32, x_39, x_8, x_9, x_10, x_11);
lean_dec_ref(x_40);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_36;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_30; lean_object* x_31; uint8_t x_43; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_17 = x_3;
} else {
 lean_dec_ref(x_3);
 x_17 = lean_box(0);
}
x_43 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(x_15);
if (x_43 == 0)
{
x_30 = x_43;
x_31 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_44; 
lean_inc(x_15);
x_44 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_15, x_5, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
x_30 = x_46;
x_31 = lean_box(0);
goto block_42;
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
block_29:
{
lean_object* x_27; 
x_27 = l_Lean_Meta_Grind_addCongrTable(x_15, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(x_1, x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_27;
}
}
block_42:
{
if (x_30 == 0)
{
lean_object* x_32; 
lean_dec(x_17);
lean_dec(x_15);
x_32 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(x_1, x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3;
x_34 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_33, x_11);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_dec(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
x_26 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_37);
x_38 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1;
lean_inc(x_15);
x_39 = l_Lean_MessageData_ofExpr(x_15);
if (lean_is_scalar(x_17)) {
 x_40 = lean_alloc_ctor(7, 2, 0);
} else {
 x_40 = x_17;
 lean_ctor_set_tag(x_40, 7);
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_33, x_40, x_9, x_10, x_11, x_12);
lean_dec_ref(x_41);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
x_26 = lean_box(0);
goto block_29;
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Meta_Grind_ParentSet_elems(x_1);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_12, x_11, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_1, x_7);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mp", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_11, x_6);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_12);
x_16 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_Grind_mkEqFalseProof(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
x_25 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8;
x_26 = l_Lean_mkApp4(x_24, x_21, x_23, x_19, x_25);
x_27 = l_Lean_Meta_Grind_closeGoal(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_12, 0);
lean_inc(x_41);
lean_dec(x_12);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_3);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Meta_Grind_mkEqFalseProof(x_44, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_3);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
x_52 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8;
x_53 = l_Lean_mkApp4(x_51, x_48, x_50, x_46, x_52);
x_54 = l_Lean_Meta_Grind_closeGoal(x_53, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_59 = x_47;
} else {
 lean_dec_ref(x_47);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_43, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_65 = x_43;
} else {
 lean_dec_ref(x_43);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolFalse;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_13);
x_16 = l_Lean_Meta_mkDecide(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2;
x_21 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3;
lean_inc(x_13);
x_23 = l_Lean_mkApp3(x_20, x_13, x_21, x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
x_25 = l_Lean_mkApp4(x_24, x_13, x_19, x_23, x_15);
x_26 = l_Lean_Meta_Grind_closeGoal(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = lean_st_ref_get(x_5);
lean_inc(x_15);
x_18 = l_Lean_Meta_Grind_Goal_getENode(x_17, x_15, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_ctor_get(x_19, 3);
x_25 = lean_ctor_get(x_19, 4);
x_26 = lean_ctor_get(x_19, 5);
x_27 = lean_ctor_get(x_19, 6);
x_28 = lean_ctor_get(x_19, 7);
x_29 = lean_ctor_get(x_19, 8);
x_30 = lean_ctor_get(x_19, 9);
x_31 = lean_ctor_get(x_19, 10);
x_32 = lean_nat_dec_lt(x_30, x_1);
lean_dec(x_30);
if (x_32 == 0)
{
lean_free_object(x_19);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_15);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_2;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_34; 
lean_inc(x_1);
lean_ctor_set(x_19, 9, x_1);
lean_inc(x_15);
x_34 = l_Lean_Meta_Grind_setENode___redArg(x_15, x_19, x_5);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_dec_ref(x_35);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_2;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
return x_34;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
x_39 = lean_ctor_get(x_19, 2);
x_40 = lean_ctor_get(x_19, 3);
x_41 = lean_ctor_get(x_19, 4);
x_42 = lean_ctor_get(x_19, 5);
x_43 = lean_ctor_get_uint8(x_19, sizeof(void*)*11);
x_44 = lean_ctor_get(x_19, 6);
x_45 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 1);
x_46 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 2);
x_47 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 3);
x_48 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 4);
x_49 = lean_ctor_get(x_19, 7);
x_50 = lean_ctor_get(x_19, 8);
x_51 = lean_ctor_get(x_19, 9);
x_52 = lean_ctor_get(x_19, 10);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_53 = lean_nat_dec_lt(x_51, x_1);
lean_dec(x_51);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_15);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_2;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_inc(x_1);
x_55 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_38);
lean_ctor_set(x_55, 2, x_39);
lean_ctor_set(x_55, 3, x_40);
lean_ctor_set(x_55, 4, x_41);
lean_ctor_set(x_55, 5, x_42);
lean_ctor_set(x_55, 6, x_44);
lean_ctor_set(x_55, 7, x_49);
lean_ctor_set(x_55, 8, x_50);
lean_ctor_set(x_55, 9, x_1);
lean_ctor_set(x_55, 10, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*11, x_43);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 1, x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 2, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 3, x_47);
lean_ctor_set_uint8(x_55, sizeof(void*)*11 + 4, x_48);
lean_inc(x_15);
x_56 = l_Lean_Meta_Grind_setENode___redArg(x_15, x_55, x_5);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec_ref(x_56);
x_57 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_2;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_1);
return x_57;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
return x_56;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_18, 0);
lean_inc(x_60);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_get(x_2);
x_12 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 12);
lean_inc_ref(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_Grind_ParentSet_elems(x_14);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_15, x_17, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
}
else
{
return x_18;
}
}
else
{
uint8_t x_22; 
lean_dec_ref(x_11);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curr: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_inc(x_4);
x_44 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_4, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_70; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
x_70 = lean_unbox(x_45);
lean_dec(x_45);
if (x_70 == 0)
{
lean_free_object(x_5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_71);
x_72 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1;
lean_inc(x_48);
x_73 = l_Lean_MessageData_ofExpr(x_48);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_73);
lean_ctor_set(x_5, 0, x_72);
lean_inc(x_4);
x_74 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_4, x_5, x_10, x_11, x_12, x_13);
lean_dec_ref(x_74);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = lean_box(0);
goto block_69;
}
else
{
uint8_t x_75; 
lean_free_object(x_5);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
block_69:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_isEqv___redArg(x_48, x_2, x_49);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = x_56;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_47);
x_61 = l_Array_reverse___redArg(x_47);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_62 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_48, x_61, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = x_56;
x_25 = lean_box(0);
goto block_43;
}
else
{
uint8_t x_63; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_101; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_101 = lean_unbox(x_45);
lean_dec(x_45);
if (x_101 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = x_13;
x_88 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_102; 
x_102 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_102);
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1;
lean_inc(x_79);
x_104 = l_Lean_MessageData_ofExpr(x_79);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_4);
x_106 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_4, x_105, x_10, x_11, x_12, x_13);
lean_dec_ref(x_106);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = x_13;
x_88 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
block_100:
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_isEqv___redArg(x_79, x_2, x_80);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_15 = x_78;
x_16 = x_79;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_83;
x_21 = x_84;
x_22 = x_85;
x_23 = x_86;
x_24 = x_87;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_inc(x_78);
x_92 = l_Array_reverse___redArg(x_78);
lean_inc(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
x_93 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_79, x_92, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_15 = x_78;
x_16 = x_79;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_83;
x_21 = x_84;
x_22 = x_85;
x_23 = x_86;
x_24 = x_87;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
}
block_43:
{
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
x_31 = lean_grind_internalize(x_16, x_29, x_30, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_31);
x_32 = lean_array_push(x_15, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_5 = x_33;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_16);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_inc(x_4);
x_44 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_4, x_12);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_70; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
x_70 = lean_unbox(x_45);
lean_dec(x_45);
if (x_70 == 0)
{
lean_free_object(x_5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_71);
x_72 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1;
lean_inc(x_48);
x_73 = l_Lean_MessageData_ofExpr(x_48);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_73);
lean_ctor_set(x_5, 0, x_72);
lean_inc(x_4);
x_74 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_4, x_5, x_10, x_11, x_12, x_13);
lean_dec_ref(x_74);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = x_6;
x_50 = x_7;
x_51 = x_8;
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = lean_box(0);
goto block_69;
}
else
{
uint8_t x_75; 
lean_free_object(x_5);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
block_69:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_isEqv___redArg(x_48, x_2, x_49);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = x_56;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_inc(x_47);
x_61 = l_Array_reverse___redArg(x_47);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_62 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_48, x_61, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
x_23 = x_55;
x_24 = x_56;
x_25 = lean_box(0);
goto block_43;
}
else
{
uint8_t x_63; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_101; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_101 = lean_unbox(x_45);
lean_dec(x_45);
if (x_101 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = x_13;
x_88 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_102; 
x_102 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_102);
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1;
lean_inc(x_79);
x_104 = l_Lean_MessageData_ofExpr(x_79);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_4);
x_106 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_4, x_105, x_10, x_11, x_12, x_13);
lean_dec_ref(x_106);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = x_6;
x_81 = x_7;
x_82 = x_8;
x_83 = x_9;
x_84 = x_10;
x_85 = x_11;
x_86 = x_12;
x_87 = x_13;
x_88 = lean_box(0);
goto block_100;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
return x_109;
}
}
block_100:
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_isEqv___redArg(x_79, x_2, x_80);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_15 = x_78;
x_16 = x_79;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_83;
x_21 = x_84;
x_22 = x_85;
x_23 = x_86;
x_24 = x_87;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_inc(x_78);
x_92 = l_Array_reverse___redArg(x_78);
lean_inc(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
x_93 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_79, x_92, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_15 = x_78;
x_16 = x_79;
x_17 = x_80;
x_18 = x_81;
x_19 = x_82;
x_20 = x_83;
x_21 = x_84;
x_22 = x_85;
x_23 = x_86;
x_24 = x_87;
x_25 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
}
block_43:
{
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(0);
x_31 = lean_grind_internalize(x_16, x_29, x_30, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_31);
x_32 = lean_array_push(x_15, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0(x_1, x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_16);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parent: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
lean_inc(x_3);
x_44 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_3, x_19);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_47 = lean_unbox(x_45);
lean_dec(x_45);
if (x_47 == 0)
{
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_26 = x_46;
x_27 = x_23;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Meta_Grind_updateLastTag(x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_48);
x_49 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2;
lean_inc(x_23);
x_50 = l_Lean_MessageData_ofExpr(x_23);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_3);
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_3, x_51, x_17, x_18, x_19, x_20);
lean_dec_ref(x_52);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_26 = x_46;
x_27 = x_23;
x_28 = x_13;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = lean_box(0);
goto block_43;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
return x_48;
}
}
block_43:
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_25)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_25;
 lean_ctor_set_tag(x_37, 0);
}
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_inc(x_3);
x_38 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(x_23, x_1, x_2, x_3, x_37, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35);
lean_dec(x_23);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
{
lean_object* _tmp_10 = x_24;
lean_object* _tmp_11 = x_10;
x_11 = _tmp_10;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_24; 
x_24 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_13, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
lean_inc(x_3);
x_45 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_3, x_20);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_48 = lean_unbox(x_46);
lean_dec(x_46);
if (x_48 == 0)
{
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_24);
x_27 = x_47;
x_28 = x_24;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_49; 
x_49 = l_Lean_Meta_Grind_updateLastTag(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_49);
x_50 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2;
lean_inc(x_24);
x_51 = l_Lean_MessageData_ofExpr(x_24);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_3);
x_53 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_3, x_52, x_18, x_19, x_20, x_21);
lean_dec_ref(x_53);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_24);
x_27 = x_47;
x_28 = x_24;
x_29 = x_14;
x_30 = x_15;
x_31 = x_16;
x_32 = x_17;
x_33 = x_18;
x_34 = x_19;
x_35 = x_20;
x_36 = x_21;
x_37 = lean_box(0);
goto block_44;
}
else
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
return x_49;
}
}
block_44:
{
lean_object* x_38; lean_object* x_39; 
if (lean_is_scalar(x_26)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_26;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_inc(x_3);
x_39 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(x_24, x_1, x_2, x_3, x_38, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_24);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
x_40 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25, x_10, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_24; 
x_24 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_24;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fn: ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", parents: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_13, x_12);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_49; 
lean_inc(x_3);
x_26 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_3, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_array_uget(x_11, x_13);
x_49 = lean_unbox(x_27);
lean_dec(x_27);
if (x_49 == 0)
{
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = x_15;
x_30 = x_16;
x_31 = x_17;
x_32 = x_18;
x_33 = x_19;
x_34 = x_20;
x_35 = x_21;
x_36 = x_22;
x_37 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Meta_Grind_updateLastTag(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Meta_Grind_getParents___redArg(x_28, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1;
lean_inc_ref(x_28);
x_54 = l_Lean_MessageData_ofExpr(x_28);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_Grind_ParentSet_elems(x_52);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(x_58, x_59);
x_61 = l_Lean_MessageData_ofList(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_3);
x_63 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_3, x_62, x_19, x_20, x_21, x_22);
lean_dec_ref(x_63);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = x_15;
x_30 = x_16;
x_31 = x_17;
x_32 = x_18;
x_33 = x_19;
x_34 = x_20;
x_35 = x_21;
x_36 = x_22;
x_37 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_64; 
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
return x_50;
}
}
block_48:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_getParents___redArg(x_28, x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Meta_Grind_ParentSet_elems(x_39);
lean_dec(x_39);
lean_inc(x_40);
lean_inc(x_3);
x_41 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40, x_40, x_10, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
size_t x_42; size_t x_43; 
lean_dec_ref(x_41);
x_42 = 1;
x_43 = lean_usize_add(x_13, x_42);
{
size_t _tmp_12 = x_43;
lean_object* _tmp_13 = x_10;
x_13 = _tmp_12;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
return x_41;
}
}
else
{
uint8_t x_45; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_13, x_12);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_49; 
lean_inc(x_3);
x_26 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_3, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_array_uget(x_11, x_13);
x_49 = lean_unbox(x_27);
lean_dec(x_27);
if (x_49 == 0)
{
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = x_15;
x_30 = x_16;
x_31 = x_17;
x_32 = x_18;
x_33 = x_19;
x_34 = x_20;
x_35 = x_21;
x_36 = x_22;
x_37 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Meta_Grind_updateLastTag(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Meta_Grind_getParents___redArg(x_28, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1;
lean_inc_ref(x_28);
x_54 = l_Lean_MessageData_ofExpr(x_28);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_Grind_ParentSet_elems(x_52);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(x_58, x_59);
x_61 = l_Lean_MessageData_ofList(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_3);
x_63 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_3, x_62, x_19, x_20, x_21, x_22);
lean_dec_ref(x_63);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = x_15;
x_30 = x_16;
x_31 = x_17;
x_32 = x_18;
x_33 = x_19;
x_34 = x_20;
x_35 = x_21;
x_36 = x_22;
x_37 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_64; 
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
return x_50;
}
}
block_48:
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_getParents___redArg(x_28, x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Meta_Grind_ParentSet_elems(x_39);
lean_dec(x_39);
lean_inc(x_40);
lean_inc(x_3);
x_41 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40, x_40, x_10, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
size_t x_42; size_t x_43; lean_object* x_44; 
lean_dec_ref(x_41);
x_42 = 1;
x_43 = lean_usize_add(x_13, x_42);
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43, x_10, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_44;
}
else
{
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
return x_41;
}
}
else
{
uint8_t x_45; 
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateBeta___closed__0;
x_2 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1;
x_3 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fns: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateBeta___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", lams: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateBeta___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = l_Array_isEmpty___redArg(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_3);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_Array_back_x21___redArg(x_14, x_1);
x_16 = l_Lean_Meta_Grind_Goal_getRoot(x_13, x_15, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_40; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_propagateBeta___closed__1;
x_19 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_propagateBeta___closed__2;
x_22 = l_Lean_Meta_Grind_propagateBeta___closed__3;
x_40 = lean_unbox(x_20);
lean_dec(x_20);
if (x_40 == 0)
{
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = lean_box(0);
goto block_39;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_41);
x_42 = l_Lean_Meta_Grind_propagateBeta___closed__5;
lean_inc_ref(x_2);
x_43 = lean_array_to_list(x_2);
x_44 = lean_box(0);
x_45 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(x_43, x_44);
x_46 = l_Lean_MessageData_ofList(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Grind_propagateBeta___closed__7;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc_ref(x_1);
x_50 = lean_array_to_list(x_1);
x_51 = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__4(x_50, x_44);
x_52 = l_Lean_MessageData_ofList(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_18, x_53, x_7, x_8, x_9, x_10);
lean_dec_ref(x_54);
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = lean_box(0);
goto block_39;
}
else
{
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_41;
}
}
block_39:
{
lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_32 = lean_box(0);
x_33 = lean_array_size(x_2);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5(x_17, x_1, x_18, x_21, x_22, x_21, x_22, x_22, x_21, x_32, x_2, x_33, x_34, x_32, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_dec(x_17);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; 
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_32);
return x_38;
}
}
else
{
return x_35;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
return x_16;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_16, 0);
lean_inc(x_56);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
lean_object* x_24; 
x_24 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
lean_object* x_23; 
x_23 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
lean_object* x_24; 
x_24 = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_25 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24, x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_25 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24, x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateBeta(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_14) == 6)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_16 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_1, x_15);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
lean_dec_ref(x_14);
x_8 = x_2;
goto block_12;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(x_2, x_5, x_4, x_1, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
return x_3;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Inhabited", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2;
x_2 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Subsingleton", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_7, x_6);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_8);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_array_uget(x_5, x_7);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_27);
x_29 = l_Lean_Meta_getLevel(x_27, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1;
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_inc_ref(x_33);
x_34 = l_Lean_mkConst(x_31, x_33);
lean_inc_ref(x_27);
x_35 = l_Lean_Expr_app___override(x_34, x_27);
x_36 = lean_box(0);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_37 = l_Lean_Meta_synthInstance_x3f(x_35, x_36, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_83; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_83 = l_Lean_Expr_hasLooseBVars(x_28);
if (x_83 == 0)
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5;
lean_inc_ref(x_33);
x_85 = l_Lean_mkConst(x_84, x_33);
lean_inc_ref(x_27);
x_86 = l_Lean_Expr_app___override(x_85, x_27);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_87 = l_Lean_Meta_synthInstance_x3f(x_86, x_36, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_dec_ref(x_88);
if (x_83 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_40 = x_9;
x_41 = x_10;
x_42 = x_11;
x_43 = x_12;
x_44 = x_13;
x_45 = x_14;
x_46 = x_15;
x_47 = x_16;
x_48 = lean_box(0);
goto block_82;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
block_82:
{
lean_object* x_49; 
x_49 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(x_2, x_27);
lean_dec_ref(x_27);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_28);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_50) == 6)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_50, 2);
lean_inc_ref(x_52);
lean_dec_ref(x_50);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3;
x_54 = l_Lean_mkConst(x_53, x_33);
x_55 = l_Lean_mkAppB(x_54, x_51, x_39);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
x_56 = l_Lean_Meta_Grind_preprocessLight(x_55, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_array_fget_borrowed(x_3, x_4);
x_59 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc_ref(x_59);
lean_inc_ref(x_58);
x_60 = lean_grind_mk_eq_proof(x_58, x_59, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_57);
x_62 = l_Lean_Meta_mkCongrFun(x_61, x_57, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_expr_instantiate1(x_28, x_57);
lean_dec_ref(x_28);
x_65 = lean_expr_instantiate1(x_52, x_57);
lean_dec(x_57);
lean_dec_ref(x_52);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
x_66 = l_Lean_Meta_mkEq(x_64, x_65, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_mkExpectedPropHint(x_63, x_67);
lean_inc(x_4);
x_69 = l_Lean_Meta_Grind_pushNewFact(x_68, x_4, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_63);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_57);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_28);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_62);
if (x_73 == 0)
{
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_57);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_28);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_60);
if (x_76 == 0)
{
return x_60;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_28);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_56);
if (x_79 == 0)
{
return x_56;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_56, 0);
lean_inc(x_80);
lean_dec(x_56);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_33);
lean_dec_ref(x_28);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_33);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_92 = !lean_is_exclusive(x_37);
if (x_92 == 0)
{
return x_37;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_37, 0);
lean_inc(x_93);
lean_dec(x_37);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_29);
if (x_95 == 0)
{
return x_29;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_29, 0);
lean_inc(x_96);
lean_dec(x_29);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_dec_ref(x_26);
x_18 = x_1;
x_19 = lean_box(0);
goto block_23;
}
}
block_23:
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_7 = x_21;
x_8 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_eq(x_15, x_13);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = lean_array_size(x_1);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(x_17, x_2, x_1, x_13, x_1, x_18, x_19, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
return x_23;
}
}
else
{
return x_20;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget_borrowed(x_2, x_4);
lean_inc_ref(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_14 = lean_array_fget_borrowed(x_3, x_4);
lean_dec(x_4);
lean_inc(x_14);
lean_inc_ref(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg(x_1, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_box(2);
x_8 = 5;
x_9 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_3, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_6, x_11);
lean_dec(x_11);
lean_dec_ref(x_6);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_16 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
lean_inc(x_18);
x_20 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_2);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
}
}
case 1:
{
lean_object* x_23; size_t x_24; 
lean_free_object(x_2);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec_ref(x_12);
x_24 = lean_usize_shift_right(x_3, x_8);
x_2 = x_23;
x_3 = x_24;
goto _start;
}
default: 
{
lean_object* x_26; 
lean_free_object(x_2);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_26 = lean_box(0);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_box(2);
x_29 = 5;
x_30 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
x_31 = lean_usize_land(x_3, x_30);
x_32 = lean_usize_to_nat(x_31);
x_33 = lean_array_get(x_28, x_27, x_32);
lean_dec(x_32);
lean_dec_ref(x_27);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
lean_inc(x_34);
x_37 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
case 1:
{
lean_object* x_41; size_t x_42; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec_ref(x_33);
x_42 = lean_usize_shift_right(x_3, x_29);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
default: 
{
lean_object* x_44; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_44 = lean_box(0);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_46);
lean_dec_ref(x_2);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg(x_1, x_45, x_46, x_47, x_4);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_4 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_11 = lean_array_push(x_7, x_4);
x_12 = lean_array_push(x_8, x_5);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_fget_borrowed(x_7, x_3);
lean_inc_ref(x_13);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_1);
x_18 = lean_array_fset(x_7, x_3, x_4);
x_19 = lean_array_fset(x_8, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_3, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_array_push(x_21, x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_fget_borrowed(x_20, x_3);
lean_inc_ref(x_27);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_28 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_4, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_2 = x_29;
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_1);
x_33 = lean_array_fset(x_20, x_3, x_4);
x_34 = lean_array_fset(x_21, x_3, x_5);
lean_dec(x_3);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; lean_object* x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget_borrowed(x_3, x_5);
x_10 = lean_array_fget_borrowed(x_4, x_5);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 5;
x_14 = lean_unsigned_to_nat(1u);
x_15 = 1;
x_16 = lean_usize_sub(x_2, x_15);
x_17 = lean_usize_mul(x_13, x_16);
x_18 = lean_usize_shift_right(x_12, x_17);
x_19 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_20 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_6, x_18, x_2, x_9, x_10);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(x_1, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = 5;
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
x_11 = lean_usize_land(x_3, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_15 = x_2;
} else {
 lean_dec_ref(x_2);
 x_15 = lean_box(0);
}
x_16 = lean_array_fget(x_7, x_12);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_12, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc_ref(x_5);
x_26 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_5, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_16);
x_27 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_24, x_25, x_5, x_6);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_19 = x_28;
goto block_22;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_5);
x_19 = x_16;
goto block_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
lean_inc(x_29);
lean_inc_ref(x_5);
x_31 = l_Lean_Meta_Grind_instBEqCongrKey___private__1(x_1, x_5, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_29, x_30, x_5, x_6);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_19 = x_33;
goto block_22;
}
else
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_19 = x_34;
goto block_22;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_usize_shift_right(x_3, x_8);
x_38 = lean_usize_add(x_4, x_9);
x_39 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_36, x_37, x_38, x_5, x_6);
lean_ctor_set(x_16, 0, x_39);
x_19 = x_16;
goto block_22;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_usize_shift_right(x_3, x_8);
x_42 = lean_usize_add(x_4, x_9);
x_43 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_40, x_41, x_42, x_5, x_6);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_19 = x_44;
goto block_22;
}
}
default: 
{
lean_object* x_45; 
lean_dec_ref(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_6);
x_19 = x_45;
goto block_22;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_12, x_19);
lean_dec(x_12);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; size_t x_55; uint8_t x_56; 
lean_inc_ref(x_1);
x_47 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_5, x_6);
x_55 = 7;
x_56 = lean_usize_dec_le(x_55, x_4);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_47);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_dec_lt(x_57, x_58);
lean_dec(x_57);
x_48 = x_59;
goto block_54;
}
else
{
x_48 = x_56;
goto block_54;
}
block_54:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_47);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0;
x_53 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(x_1, x_4, x_49, x_50, x_51, x_52);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
return x_53;
}
else
{
lean_dec_ref(x_1);
return x_47;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; size_t x_71; uint8_t x_72; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_inc_ref(x_1);
x_63 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__3___redArg(x_1, x_62, x_5, x_6);
x_71 = 7;
x_72 = lean_usize_dec_le(x_71, x_4);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_63);
x_74 = lean_unsigned_to_nat(4u);
x_75 = lean_nat_dec_lt(x_73, x_74);
lean_dec(x_73);
x_64 = x_75;
goto block_70;
}
else
{
x_64 = x_72;
goto block_70;
}
block_70:
{
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_66);
lean_dec_ref(x_63);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0;
x_69 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(x_1, x_4, x_65, x_66, x_67, x_68);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
return x_69;
}
else
{
lean_dec_ref(x_1);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_5 = l_Lean_Meta_Grind_instHashableCongrKey___private__1(x_1, x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = 1;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
lean_inc(x_12);
x_14 = l_Lean_Meta_Grind_Goal_getENode(x_11, x_12, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_41; lean_object* x_46; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 4);
x_21 = lean_ctor_get(x_15, 5);
x_22 = lean_ctor_get_uint8(x_15, sizeof(void*)*11);
x_23 = lean_ctor_get(x_15, 6);
x_24 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 1);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 2);
x_26 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 3);
x_27 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 4);
x_28 = lean_ctor_get(x_15, 7);
x_29 = lean_ctor_get(x_15, 8);
x_30 = lean_ctor_get(x_15, 9);
x_31 = lean_ctor_get(x_15, 10);
x_32 = lean_ctor_get(x_15, 2);
lean_dec(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc_ref(x_3);
lean_inc_ref(x_19);
lean_inc_ref(x_18);
lean_ctor_set(x_15, 2, x_3);
lean_inc_ref(x_15);
lean_inc_ref(x_18);
x_46 = l_Lean_Meta_Grind_setENode___redArg(x_18, x_15, x_6);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
if (x_4 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_33 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Expr_isAppOfArity(x_18, x_47, x_48);
if (x_49 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_33 = lean_box(0);
goto block_40;
}
else
{
uint8_t x_50; 
x_50 = l_Lean_Meta_Grind_ENode_isCongrRoot(x_15);
lean_dec_ref(x_15);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_st_ref_get(x_6);
x_52 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_51, 5);
lean_inc_ref(x_53);
lean_dec_ref(x_51);
lean_inc_ref(x_18);
x_54 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_52, x_53, x_18);
if (lean_obj_tag(x_54) == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_33 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Meta_Grind_isFalseExpr___redArg(x_56, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_st_ref_take(x_6);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_60, 2);
x_63 = lean_ctor_get(x_60, 5);
x_64 = lean_box(0);
lean_inc_ref(x_18);
lean_inc_ref(x_62);
x_65 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_62, x_63, x_18, x_64);
lean_ctor_set(x_60, 5, x_65);
x_66 = lean_st_ref_set(x_6, x_60);
lean_inc_ref(x_3);
lean_inc_ref(x_19);
lean_inc_ref_n(x_18, 2);
x_67 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_67, 0, x_18);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_3);
lean_ctor_set(x_67, 3, x_18);
lean_ctor_set(x_67, 4, x_20);
lean_ctor_set(x_67, 5, x_21);
lean_ctor_set(x_67, 6, x_23);
lean_ctor_set(x_67, 7, x_28);
lean_ctor_set(x_67, 8, x_29);
lean_ctor_set(x_67, 9, x_30);
lean_ctor_set(x_67, 10, x_31);
lean_ctor_set_uint8(x_67, sizeof(void*)*11, x_22);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 1, x_24);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 2, x_25);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 3, x_26);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 4, x_27);
lean_inc_ref(x_18);
x_68 = l_Lean_Meta_Grind_setENode___redArg(x_18, x_67, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_68);
x_69 = lean_st_ref_get(x_6);
lean_inc(x_56);
x_70 = l_Lean_Meta_Grind_Goal_getENode(x_69, x_56, x_8, x_9);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 3);
lean_dec(x_73);
lean_ctor_set(x_71, 3, x_18);
x_74 = l_Lean_Meta_Grind_setENode___redArg(x_56, x_71, x_6);
x_41 = x_74;
goto block_45;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_71, 2);
x_78 = lean_ctor_get(x_71, 4);
x_79 = lean_ctor_get(x_71, 5);
x_80 = lean_ctor_get_uint8(x_71, sizeof(void*)*11);
x_81 = lean_ctor_get(x_71, 6);
x_82 = lean_ctor_get_uint8(x_71, sizeof(void*)*11 + 1);
x_83 = lean_ctor_get_uint8(x_71, sizeof(void*)*11 + 2);
x_84 = lean_ctor_get_uint8(x_71, sizeof(void*)*11 + 3);
x_85 = lean_ctor_get_uint8(x_71, sizeof(void*)*11 + 4);
x_86 = lean_ctor_get(x_71, 7);
x_87 = lean_ctor_get(x_71, 8);
x_88 = lean_ctor_get(x_71, 9);
x_89 = lean_ctor_get(x_71, 10);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_81);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_90 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_76);
lean_ctor_set(x_90, 2, x_77);
lean_ctor_set(x_90, 3, x_18);
lean_ctor_set(x_90, 4, x_78);
lean_ctor_set(x_90, 5, x_79);
lean_ctor_set(x_90, 6, x_81);
lean_ctor_set(x_90, 7, x_86);
lean_ctor_set(x_90, 8, x_87);
lean_ctor_set(x_90, 9, x_88);
lean_ctor_set(x_90, 10, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*11, x_80);
lean_ctor_set_uint8(x_90, sizeof(void*)*11 + 1, x_82);
lean_ctor_set_uint8(x_90, sizeof(void*)*11 + 2, x_83);
lean_ctor_set_uint8(x_90, sizeof(void*)*11 + 3, x_84);
lean_ctor_set_uint8(x_90, sizeof(void*)*11 + 4, x_85);
x_91 = l_Lean_Meta_Grind_setENode___redArg(x_56, x_90, x_6);
x_41 = x_91;
goto block_45;
}
}
else
{
uint8_t x_92; 
lean_dec(x_56);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_70);
if (x_92 == 0)
{
return x_70;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_70, 0);
lean_inc(x_93);
lean_dec(x_70);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_56);
lean_dec_ref(x_18);
x_41 = x_68;
goto block_45;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_95 = lean_ctor_get(x_60, 0);
x_96 = lean_ctor_get(x_60, 1);
x_97 = lean_ctor_get(x_60, 2);
x_98 = lean_ctor_get(x_60, 3);
x_99 = lean_ctor_get(x_60, 4);
x_100 = lean_ctor_get(x_60, 5);
x_101 = lean_ctor_get(x_60, 6);
x_102 = lean_ctor_get(x_60, 7);
x_103 = lean_ctor_get_uint8(x_60, sizeof(void*)*17);
x_104 = lean_ctor_get(x_60, 8);
x_105 = lean_ctor_get(x_60, 9);
x_106 = lean_ctor_get(x_60, 10);
x_107 = lean_ctor_get(x_60, 11);
x_108 = lean_ctor_get(x_60, 12);
x_109 = lean_ctor_get(x_60, 13);
x_110 = lean_ctor_get(x_60, 14);
x_111 = lean_ctor_get(x_60, 15);
x_112 = lean_ctor_get(x_60, 16);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_60);
x_113 = lean_box(0);
lean_inc_ref(x_18);
lean_inc_ref(x_97);
x_114 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_97, x_100, x_18, x_113);
x_115 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_115, 0, x_95);
lean_ctor_set(x_115, 1, x_96);
lean_ctor_set(x_115, 2, x_97);
lean_ctor_set(x_115, 3, x_98);
lean_ctor_set(x_115, 4, x_99);
lean_ctor_set(x_115, 5, x_114);
lean_ctor_set(x_115, 6, x_101);
lean_ctor_set(x_115, 7, x_102);
lean_ctor_set(x_115, 8, x_104);
lean_ctor_set(x_115, 9, x_105);
lean_ctor_set(x_115, 10, x_106);
lean_ctor_set(x_115, 11, x_107);
lean_ctor_set(x_115, 12, x_108);
lean_ctor_set(x_115, 13, x_109);
lean_ctor_set(x_115, 14, x_110);
lean_ctor_set(x_115, 15, x_111);
lean_ctor_set(x_115, 16, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*17, x_103);
x_116 = lean_st_ref_set(x_6, x_115);
lean_inc_ref(x_3);
lean_inc_ref(x_19);
lean_inc_ref_n(x_18, 2);
x_117 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_117, 0, x_18);
lean_ctor_set(x_117, 1, x_19);
lean_ctor_set(x_117, 2, x_3);
lean_ctor_set(x_117, 3, x_18);
lean_ctor_set(x_117, 4, x_20);
lean_ctor_set(x_117, 5, x_21);
lean_ctor_set(x_117, 6, x_23);
lean_ctor_set(x_117, 7, x_28);
lean_ctor_set(x_117, 8, x_29);
lean_ctor_set(x_117, 9, x_30);
lean_ctor_set(x_117, 10, x_31);
lean_ctor_set_uint8(x_117, sizeof(void*)*11, x_22);
lean_ctor_set_uint8(x_117, sizeof(void*)*11 + 1, x_24);
lean_ctor_set_uint8(x_117, sizeof(void*)*11 + 2, x_25);
lean_ctor_set_uint8(x_117, sizeof(void*)*11 + 3, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*11 + 4, x_27);
lean_inc_ref(x_18);
x_118 = l_Lean_Meta_Grind_setENode___redArg(x_18, x_117, x_6);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_118);
x_119 = lean_st_ref_get(x_6);
lean_inc(x_56);
x_120 = l_Lean_Meta_Grind_Goal_getENode(x_119, x_56, x_8, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_121, 2);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_121, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 5);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_121, sizeof(void*)*11);
x_128 = lean_ctor_get(x_121, 6);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_121, sizeof(void*)*11 + 1);
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*11 + 2);
x_131 = lean_ctor_get_uint8(x_121, sizeof(void*)*11 + 3);
x_132 = lean_ctor_get_uint8(x_121, sizeof(void*)*11 + 4);
x_133 = lean_ctor_get(x_121, 7);
lean_inc(x_133);
x_134 = lean_ctor_get(x_121, 8);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 9);
lean_inc(x_135);
x_136 = lean_ctor_get(x_121, 10);
lean_inc(x_136);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 lean_ctor_release(x_121, 6);
 lean_ctor_release(x_121, 7);
 lean_ctor_release(x_121, 8);
 lean_ctor_release(x_121, 9);
 lean_ctor_release(x_121, 10);
 x_137 = x_121;
} else {
 lean_dec_ref(x_121);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 11, 5);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_123);
lean_ctor_set(x_138, 2, x_124);
lean_ctor_set(x_138, 3, x_18);
lean_ctor_set(x_138, 4, x_125);
lean_ctor_set(x_138, 5, x_126);
lean_ctor_set(x_138, 6, x_128);
lean_ctor_set(x_138, 7, x_133);
lean_ctor_set(x_138, 8, x_134);
lean_ctor_set(x_138, 9, x_135);
lean_ctor_set(x_138, 10, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*11, x_127);
lean_ctor_set_uint8(x_138, sizeof(void*)*11 + 1, x_129);
lean_ctor_set_uint8(x_138, sizeof(void*)*11 + 2, x_130);
lean_ctor_set_uint8(x_138, sizeof(void*)*11 + 3, x_131);
lean_ctor_set_uint8(x_138, sizeof(void*)*11 + 4, x_132);
x_139 = l_Lean_Meta_Grind_setENode___redArg(x_56, x_138, x_6);
x_41 = x_139;
goto block_45;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_56);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_140 = lean_ctor_get(x_120, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_141 = x_120;
} else {
 lean_dec_ref(x_120);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_dec(x_56);
lean_dec_ref(x_18);
x_41 = x_118;
goto block_45;
}
}
}
else
{
lean_dec(x_56);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_33 = lean_box(0);
goto block_40;
}
}
else
{
uint8_t x_143; 
lean_dec(x_56);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_57);
if (x_143 == 0)
{
return x_57;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_57, 0);
lean_inc(x_144);
lean_dec(x_57);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_33 = lean_box(0);
goto block_40;
}
}
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
x_41 = x_46;
goto block_45;
}
block_40:
{
uint8_t x_34; 
x_34 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_19, x_1);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_12);
lean_inc(x_2);
if (lean_is_scalar(x_13)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_13;
}
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_19);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_19);
lean_dec_ref(x_3);
lean_dec(x_2);
x_37 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
if (lean_is_scalar(x_13)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_13;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_12);
if (lean_is_scalar(x_16)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_16;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
block_45:
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_33 = lean_box(0);
goto block_40;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_169; lean_object* x_174; lean_object* x_175; 
x_146 = lean_ctor_get(x_15, 0);
x_147 = lean_ctor_get(x_15, 1);
x_148 = lean_ctor_get(x_15, 3);
x_149 = lean_ctor_get(x_15, 4);
x_150 = lean_ctor_get(x_15, 5);
x_151 = lean_ctor_get_uint8(x_15, sizeof(void*)*11);
x_152 = lean_ctor_get(x_15, 6);
x_153 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 1);
x_154 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 2);
x_155 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 3);
x_156 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 4);
x_157 = lean_ctor_get(x_15, 7);
x_158 = lean_ctor_get(x_15, 8);
x_159 = lean_ctor_get(x_15, 9);
x_160 = lean_ctor_get(x_15, 10);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_152);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_15);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_152);
lean_inc(x_150);
lean_inc(x_149);
lean_inc_ref(x_3);
lean_inc_ref(x_147);
lean_inc_ref(x_146);
x_174 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_174, 0, x_146);
lean_ctor_set(x_174, 1, x_147);
lean_ctor_set(x_174, 2, x_3);
lean_ctor_set(x_174, 3, x_148);
lean_ctor_set(x_174, 4, x_149);
lean_ctor_set(x_174, 5, x_150);
lean_ctor_set(x_174, 6, x_152);
lean_ctor_set(x_174, 7, x_157);
lean_ctor_set(x_174, 8, x_158);
lean_ctor_set(x_174, 9, x_159);
lean_ctor_set(x_174, 10, x_160);
lean_ctor_set_uint8(x_174, sizeof(void*)*11, x_151);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 1, x_153);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 2, x_154);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 3, x_155);
lean_ctor_set_uint8(x_174, sizeof(void*)*11 + 4, x_156);
lean_inc_ref(x_174);
lean_inc_ref(x_146);
x_175 = l_Lean_Meta_Grind_setENode___redArg(x_146, x_174, x_6);
if (lean_obj_tag(x_175) == 0)
{
lean_dec_ref(x_175);
if (x_4 == 0)
{
lean_dec_ref(x_174);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_161 = lean_box(0);
goto block_168;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
x_177 = lean_unsigned_to_nat(3u);
x_178 = l_Lean_Expr_isAppOfArity(x_146, x_176, x_177);
if (x_178 == 0)
{
lean_dec_ref(x_174);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_161 = lean_box(0);
goto block_168;
}
else
{
uint8_t x_179; 
x_179 = l_Lean_Meta_Grind_ENode_isCongrRoot(x_174);
lean_dec_ref(x_174);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_st_ref_get(x_6);
x_181 = lean_ctor_get(x_180, 2);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_180, 5);
lean_inc_ref(x_182);
lean_dec_ref(x_180);
lean_inc_ref(x_146);
x_183 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_181, x_182, x_146);
if (lean_obj_tag(x_183) == 0)
{
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_161 = lean_box(0);
goto block_168;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lean_Meta_Grind_isFalseExpr___redArg(x_185, x_7);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_189 = lean_st_ref_take(x_6);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_189, 2);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_189, 3);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_189, 4);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_189, 5);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_189, 6);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_189, 7);
lean_inc_ref(x_197);
x_198 = lean_ctor_get_uint8(x_189, sizeof(void*)*17);
x_199 = lean_ctor_get(x_189, 8);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 9);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_189, 10);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_189, 11);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_189, 12);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_189, 13);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_189, 14);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_189, 15);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_189, 16);
lean_inc_ref(x_207);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 lean_ctor_release(x_189, 7);
 lean_ctor_release(x_189, 8);
 lean_ctor_release(x_189, 9);
 lean_ctor_release(x_189, 10);
 lean_ctor_release(x_189, 11);
 lean_ctor_release(x_189, 12);
 lean_ctor_release(x_189, 13);
 lean_ctor_release(x_189, 14);
 lean_ctor_release(x_189, 15);
 lean_ctor_release(x_189, 16);
 x_208 = x_189;
} else {
 lean_dec_ref(x_189);
 x_208 = lean_box(0);
}
x_209 = lean_box(0);
lean_inc_ref(x_146);
lean_inc_ref(x_192);
x_210 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_192, x_195, x_146, x_209);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 17, 1);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_190);
lean_ctor_set(x_211, 1, x_191);
lean_ctor_set(x_211, 2, x_192);
lean_ctor_set(x_211, 3, x_193);
lean_ctor_set(x_211, 4, x_194);
lean_ctor_set(x_211, 5, x_210);
lean_ctor_set(x_211, 6, x_196);
lean_ctor_set(x_211, 7, x_197);
lean_ctor_set(x_211, 8, x_199);
lean_ctor_set(x_211, 9, x_200);
lean_ctor_set(x_211, 10, x_201);
lean_ctor_set(x_211, 11, x_202);
lean_ctor_set(x_211, 12, x_203);
lean_ctor_set(x_211, 13, x_204);
lean_ctor_set(x_211, 14, x_205);
lean_ctor_set(x_211, 15, x_206);
lean_ctor_set(x_211, 16, x_207);
lean_ctor_set_uint8(x_211, sizeof(void*)*17, x_198);
x_212 = lean_st_ref_set(x_6, x_211);
lean_inc_ref(x_3);
lean_inc_ref(x_147);
lean_inc_ref_n(x_146, 2);
x_213 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_213, 0, x_146);
lean_ctor_set(x_213, 1, x_147);
lean_ctor_set(x_213, 2, x_3);
lean_ctor_set(x_213, 3, x_146);
lean_ctor_set(x_213, 4, x_149);
lean_ctor_set(x_213, 5, x_150);
lean_ctor_set(x_213, 6, x_152);
lean_ctor_set(x_213, 7, x_157);
lean_ctor_set(x_213, 8, x_158);
lean_ctor_set(x_213, 9, x_159);
lean_ctor_set(x_213, 10, x_160);
lean_ctor_set_uint8(x_213, sizeof(void*)*11, x_151);
lean_ctor_set_uint8(x_213, sizeof(void*)*11 + 1, x_153);
lean_ctor_set_uint8(x_213, sizeof(void*)*11 + 2, x_154);
lean_ctor_set_uint8(x_213, sizeof(void*)*11 + 3, x_155);
lean_ctor_set_uint8(x_213, sizeof(void*)*11 + 4, x_156);
lean_inc_ref(x_146);
x_214 = l_Lean_Meta_Grind_setENode___redArg(x_146, x_213, x_6);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec_ref(x_214);
x_215 = lean_st_ref_get(x_6);
lean_inc(x_185);
x_216 = l_Lean_Meta_Grind_Goal_getENode(x_215, x_185, x_8, x_9);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_217, 2);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_217, 4);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 5);
lean_inc(x_222);
x_223 = lean_ctor_get_uint8(x_217, sizeof(void*)*11);
x_224 = lean_ctor_get(x_217, 6);
lean_inc(x_224);
x_225 = lean_ctor_get_uint8(x_217, sizeof(void*)*11 + 1);
x_226 = lean_ctor_get_uint8(x_217, sizeof(void*)*11 + 2);
x_227 = lean_ctor_get_uint8(x_217, sizeof(void*)*11 + 3);
x_228 = lean_ctor_get_uint8(x_217, sizeof(void*)*11 + 4);
x_229 = lean_ctor_get(x_217, 7);
lean_inc(x_229);
x_230 = lean_ctor_get(x_217, 8);
lean_inc(x_230);
x_231 = lean_ctor_get(x_217, 9);
lean_inc(x_231);
x_232 = lean_ctor_get(x_217, 10);
lean_inc(x_232);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 lean_ctor_release(x_217, 6);
 lean_ctor_release(x_217, 7);
 lean_ctor_release(x_217, 8);
 lean_ctor_release(x_217, 9);
 lean_ctor_release(x_217, 10);
 x_233 = x_217;
} else {
 lean_dec_ref(x_217);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 11, 5);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_218);
lean_ctor_set(x_234, 1, x_219);
lean_ctor_set(x_234, 2, x_220);
lean_ctor_set(x_234, 3, x_146);
lean_ctor_set(x_234, 4, x_221);
lean_ctor_set(x_234, 5, x_222);
lean_ctor_set(x_234, 6, x_224);
lean_ctor_set(x_234, 7, x_229);
lean_ctor_set(x_234, 8, x_230);
lean_ctor_set(x_234, 9, x_231);
lean_ctor_set(x_234, 10, x_232);
lean_ctor_set_uint8(x_234, sizeof(void*)*11, x_223);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 1, x_225);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 2, x_226);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 3, x_227);
lean_ctor_set_uint8(x_234, sizeof(void*)*11 + 4, x_228);
x_235 = l_Lean_Meta_Grind_setENode___redArg(x_185, x_234, x_6);
x_169 = x_235;
goto block_173;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_185);
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_236 = lean_ctor_get(x_216, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_237 = x_216;
} else {
 lean_dec_ref(x_216);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
}
else
{
lean_dec(x_185);
lean_dec_ref(x_146);
x_169 = x_214;
goto block_173;
}
}
else
{
lean_dec(x_185);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_161 = lean_box(0);
goto block_168;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_185);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_239 = lean_ctor_get(x_186, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_240 = x_186;
} else {
 lean_dec_ref(x_186);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
}
else
{
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_161 = lean_box(0);
goto block_168;
}
}
}
}
else
{
lean_dec_ref(x_174);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec_ref(x_146);
x_169 = x_175;
goto block_173;
}
block_168:
{
uint8_t x_162; 
x_162 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_147, x_1);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_16);
lean_dec(x_12);
lean_inc(x_2);
if (lean_is_scalar(x_13)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_13;
}
lean_ctor_set(x_163, 0, x_2);
lean_ctor_set(x_163, 1, x_147);
x_5 = x_163;
goto _start;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_147);
lean_dec_ref(x_3);
lean_dec(x_2);
x_165 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
if (lean_is_scalar(x_13)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_13;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_12);
if (lean_is_scalar(x_16)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_16;
}
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
block_173:
{
if (lean_obj_tag(x_169) == 0)
{
lean_dec_ref(x_169);
x_161 = lean_box(0);
goto block_168;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec_ref(x_147);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_170);
return x_172;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_14);
if (x_242 == 0)
{
return x_14;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_14, 0);
lean_inc(x_243);
lean_dec(x_14);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_ref_get(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
lean_inc(x_16);
x_18 = l_Lean_Meta_Grind_Goal_getENode(x_15, x_16, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_45; lean_object* x_50; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 4);
x_25 = lean_ctor_get(x_19, 5);
x_26 = lean_ctor_get_uint8(x_19, sizeof(void*)*11);
x_27 = lean_ctor_get(x_19, 6);
x_28 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 1);
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 2);
x_30 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 3);
x_31 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 4);
x_32 = lean_ctor_get(x_19, 7);
x_33 = lean_ctor_get(x_19, 8);
x_34 = lean_ctor_get(x_19, 9);
x_35 = lean_ctor_get(x_19, 10);
x_36 = lean_ctor_get(x_19, 2);
lean_dec(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
lean_inc_ref(x_22);
lean_ctor_set(x_19, 2, x_3);
lean_inc_ref(x_19);
lean_inc_ref(x_22);
x_50 = l_Lean_Meta_Grind_setENode___redArg(x_22, x_19, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
if (x_4 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_37 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Expr_isAppOfArity(x_22, x_51, x_52);
if (x_53 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_37 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_54; 
x_54 = l_Lean_Meta_Grind_ENode_isCongrRoot(x_19);
lean_dec_ref(x_19);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_st_ref_get(x_6);
x_56 = lean_ctor_get(x_55, 2);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_55, 5);
lean_inc_ref(x_57);
lean_dec_ref(x_55);
lean_inc_ref(x_22);
x_58 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_56, x_57, x_22);
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_37 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Meta_Grind_isFalseExpr___redArg(x_60, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_st_ref_take(x_6);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_64, 2);
x_67 = lean_ctor_get(x_64, 5);
x_68 = lean_box(0);
lean_inc_ref(x_22);
lean_inc_ref(x_66);
x_69 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_66, x_67, x_22, x_68);
lean_ctor_set(x_64, 5, x_69);
x_70 = lean_st_ref_set(x_6, x_64);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
lean_inc_ref_n(x_22, 2);
x_71 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_23);
lean_ctor_set(x_71, 2, x_3);
lean_ctor_set(x_71, 3, x_22);
lean_ctor_set(x_71, 4, x_24);
lean_ctor_set(x_71, 5, x_25);
lean_ctor_set(x_71, 6, x_27);
lean_ctor_set(x_71, 7, x_32);
lean_ctor_set(x_71, 8, x_33);
lean_ctor_set(x_71, 9, x_34);
lean_ctor_set(x_71, 10, x_35);
lean_ctor_set_uint8(x_71, sizeof(void*)*11, x_26);
lean_ctor_set_uint8(x_71, sizeof(void*)*11 + 1, x_28);
lean_ctor_set_uint8(x_71, sizeof(void*)*11 + 2, x_29);
lean_ctor_set_uint8(x_71, sizeof(void*)*11 + 3, x_30);
lean_ctor_set_uint8(x_71, sizeof(void*)*11 + 4, x_31);
lean_inc_ref(x_22);
x_72 = l_Lean_Meta_Grind_setENode___redArg(x_22, x_71, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_72);
x_73 = lean_st_ref_get(x_6);
lean_inc(x_60);
x_74 = l_Lean_Meta_Grind_Goal_getENode(x_73, x_60, x_12, x_13);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 3);
lean_dec(x_77);
lean_ctor_set(x_75, 3, x_22);
x_78 = l_Lean_Meta_Grind_setENode___redArg(x_60, x_75, x_6);
x_45 = x_78;
goto block_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
x_81 = lean_ctor_get(x_75, 2);
x_82 = lean_ctor_get(x_75, 4);
x_83 = lean_ctor_get(x_75, 5);
x_84 = lean_ctor_get_uint8(x_75, sizeof(void*)*11);
x_85 = lean_ctor_get(x_75, 6);
x_86 = lean_ctor_get_uint8(x_75, sizeof(void*)*11 + 1);
x_87 = lean_ctor_get_uint8(x_75, sizeof(void*)*11 + 2);
x_88 = lean_ctor_get_uint8(x_75, sizeof(void*)*11 + 3);
x_89 = lean_ctor_get_uint8(x_75, sizeof(void*)*11 + 4);
x_90 = lean_ctor_get(x_75, 7);
x_91 = lean_ctor_get(x_75, 8);
x_92 = lean_ctor_get(x_75, 9);
x_93 = lean_ctor_get(x_75, 10);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_94 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_80);
lean_ctor_set(x_94, 2, x_81);
lean_ctor_set(x_94, 3, x_22);
lean_ctor_set(x_94, 4, x_82);
lean_ctor_set(x_94, 5, x_83);
lean_ctor_set(x_94, 6, x_85);
lean_ctor_set(x_94, 7, x_90);
lean_ctor_set(x_94, 8, x_91);
lean_ctor_set(x_94, 9, x_92);
lean_ctor_set(x_94, 10, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*11, x_84);
lean_ctor_set_uint8(x_94, sizeof(void*)*11 + 1, x_86);
lean_ctor_set_uint8(x_94, sizeof(void*)*11 + 2, x_87);
lean_ctor_set_uint8(x_94, sizeof(void*)*11 + 3, x_88);
lean_ctor_set_uint8(x_94, sizeof(void*)*11 + 4, x_89);
x_95 = l_Lean_Meta_Grind_setENode___redArg(x_60, x_94, x_6);
x_45 = x_95;
goto block_49;
}
}
else
{
uint8_t x_96; 
lean_dec(x_60);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_74);
if (x_96 == 0)
{
return x_74;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_74, 0);
lean_inc(x_97);
lean_dec(x_74);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_dec(x_60);
lean_dec_ref(x_22);
x_45 = x_72;
goto block_49;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_99 = lean_ctor_get(x_64, 0);
x_100 = lean_ctor_get(x_64, 1);
x_101 = lean_ctor_get(x_64, 2);
x_102 = lean_ctor_get(x_64, 3);
x_103 = lean_ctor_get(x_64, 4);
x_104 = lean_ctor_get(x_64, 5);
x_105 = lean_ctor_get(x_64, 6);
x_106 = lean_ctor_get(x_64, 7);
x_107 = lean_ctor_get_uint8(x_64, sizeof(void*)*17);
x_108 = lean_ctor_get(x_64, 8);
x_109 = lean_ctor_get(x_64, 9);
x_110 = lean_ctor_get(x_64, 10);
x_111 = lean_ctor_get(x_64, 11);
x_112 = lean_ctor_get(x_64, 12);
x_113 = lean_ctor_get(x_64, 13);
x_114 = lean_ctor_get(x_64, 14);
x_115 = lean_ctor_get(x_64, 15);
x_116 = lean_ctor_get(x_64, 16);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_64);
x_117 = lean_box(0);
lean_inc_ref(x_22);
lean_inc_ref(x_101);
x_118 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_101, x_104, x_22, x_117);
x_119 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_119, 0, x_99);
lean_ctor_set(x_119, 1, x_100);
lean_ctor_set(x_119, 2, x_101);
lean_ctor_set(x_119, 3, x_102);
lean_ctor_set(x_119, 4, x_103);
lean_ctor_set(x_119, 5, x_118);
lean_ctor_set(x_119, 6, x_105);
lean_ctor_set(x_119, 7, x_106);
lean_ctor_set(x_119, 8, x_108);
lean_ctor_set(x_119, 9, x_109);
lean_ctor_set(x_119, 10, x_110);
lean_ctor_set(x_119, 11, x_111);
lean_ctor_set(x_119, 12, x_112);
lean_ctor_set(x_119, 13, x_113);
lean_ctor_set(x_119, 14, x_114);
lean_ctor_set(x_119, 15, x_115);
lean_ctor_set(x_119, 16, x_116);
lean_ctor_set_uint8(x_119, sizeof(void*)*17, x_107);
x_120 = lean_st_ref_set(x_6, x_119);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
lean_inc_ref_n(x_22, 2);
x_121 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_121, 0, x_22);
lean_ctor_set(x_121, 1, x_23);
lean_ctor_set(x_121, 2, x_3);
lean_ctor_set(x_121, 3, x_22);
lean_ctor_set(x_121, 4, x_24);
lean_ctor_set(x_121, 5, x_25);
lean_ctor_set(x_121, 6, x_27);
lean_ctor_set(x_121, 7, x_32);
lean_ctor_set(x_121, 8, x_33);
lean_ctor_set(x_121, 9, x_34);
lean_ctor_set(x_121, 10, x_35);
lean_ctor_set_uint8(x_121, sizeof(void*)*11, x_26);
lean_ctor_set_uint8(x_121, sizeof(void*)*11 + 1, x_28);
lean_ctor_set_uint8(x_121, sizeof(void*)*11 + 2, x_29);
lean_ctor_set_uint8(x_121, sizeof(void*)*11 + 3, x_30);
lean_ctor_set_uint8(x_121, sizeof(void*)*11 + 4, x_31);
lean_inc_ref(x_22);
x_122 = l_Lean_Meta_Grind_setENode___redArg(x_22, x_121, x_6);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_122);
x_123 = lean_st_ref_get(x_6);
lean_inc(x_60);
x_124 = l_Lean_Meta_Grind_Goal_getENode(x_123, x_60, x_12, x_13);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 2);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 5);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_125, sizeof(void*)*11);
x_132 = lean_ctor_get(x_125, 6);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_125, sizeof(void*)*11 + 1);
x_134 = lean_ctor_get_uint8(x_125, sizeof(void*)*11 + 2);
x_135 = lean_ctor_get_uint8(x_125, sizeof(void*)*11 + 3);
x_136 = lean_ctor_get_uint8(x_125, sizeof(void*)*11 + 4);
x_137 = lean_ctor_get(x_125, 7);
lean_inc(x_137);
x_138 = lean_ctor_get(x_125, 8);
lean_inc(x_138);
x_139 = lean_ctor_get(x_125, 9);
lean_inc(x_139);
x_140 = lean_ctor_get(x_125, 10);
lean_inc(x_140);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 lean_ctor_release(x_125, 6);
 lean_ctor_release(x_125, 7);
 lean_ctor_release(x_125, 8);
 lean_ctor_release(x_125, 9);
 lean_ctor_release(x_125, 10);
 x_141 = x_125;
} else {
 lean_dec_ref(x_125);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 11, 5);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_126);
lean_ctor_set(x_142, 1, x_127);
lean_ctor_set(x_142, 2, x_128);
lean_ctor_set(x_142, 3, x_22);
lean_ctor_set(x_142, 4, x_129);
lean_ctor_set(x_142, 5, x_130);
lean_ctor_set(x_142, 6, x_132);
lean_ctor_set(x_142, 7, x_137);
lean_ctor_set(x_142, 8, x_138);
lean_ctor_set(x_142, 9, x_139);
lean_ctor_set(x_142, 10, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*11, x_131);
lean_ctor_set_uint8(x_142, sizeof(void*)*11 + 1, x_133);
lean_ctor_set_uint8(x_142, sizeof(void*)*11 + 2, x_134);
lean_ctor_set_uint8(x_142, sizeof(void*)*11 + 3, x_135);
lean_ctor_set_uint8(x_142, sizeof(void*)*11 + 4, x_136);
x_143 = l_Lean_Meta_Grind_setENode___redArg(x_60, x_142, x_6);
x_45 = x_143;
goto block_49;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_60);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
}
else
{
lean_dec(x_60);
lean_dec_ref(x_22);
x_45 = x_122;
goto block_49;
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_37 = lean_box(0);
goto block_44;
}
}
else
{
uint8_t x_147; 
lean_dec(x_60);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_61);
if (x_147 == 0)
{
return x_61;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_61, 0);
lean_inc(x_148);
lean_dec(x_61);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_37 = lean_box(0);
goto block_44;
}
}
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_45 = x_50;
goto block_49;
}
block_44:
{
uint8_t x_38; 
x_38 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_23, x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
lean_dec(x_16);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_17;
}
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_23);
x_40 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(x_1, x_2, x_3, x_4, x_39, x_6, x_8, x_12, x_13);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_23);
lean_dec_ref(x_3);
lean_dec(x_2);
x_41 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
if (lean_is_scalar(x_17)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_17;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_16);
if (lean_is_scalar(x_20)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_20;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
block_49:
{
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_37 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_46; 
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_173; lean_object* x_178; lean_object* x_179; 
x_150 = lean_ctor_get(x_19, 0);
x_151 = lean_ctor_get(x_19, 1);
x_152 = lean_ctor_get(x_19, 3);
x_153 = lean_ctor_get(x_19, 4);
x_154 = lean_ctor_get(x_19, 5);
x_155 = lean_ctor_get_uint8(x_19, sizeof(void*)*11);
x_156 = lean_ctor_get(x_19, 6);
x_157 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 1);
x_158 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 2);
x_159 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 3);
x_160 = lean_ctor_get_uint8(x_19, sizeof(void*)*11 + 4);
x_161 = lean_ctor_get(x_19, 7);
x_162 = lean_ctor_get(x_19, 8);
x_163 = lean_ctor_get(x_19, 9);
x_164 = lean_ctor_get(x_19, 10);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_156);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_19);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_156);
lean_inc(x_154);
lean_inc(x_153);
lean_inc_ref(x_3);
lean_inc_ref(x_151);
lean_inc_ref(x_150);
x_178 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_178, 0, x_150);
lean_ctor_set(x_178, 1, x_151);
lean_ctor_set(x_178, 2, x_3);
lean_ctor_set(x_178, 3, x_152);
lean_ctor_set(x_178, 4, x_153);
lean_ctor_set(x_178, 5, x_154);
lean_ctor_set(x_178, 6, x_156);
lean_ctor_set(x_178, 7, x_161);
lean_ctor_set(x_178, 8, x_162);
lean_ctor_set(x_178, 9, x_163);
lean_ctor_set(x_178, 10, x_164);
lean_ctor_set_uint8(x_178, sizeof(void*)*11, x_155);
lean_ctor_set_uint8(x_178, sizeof(void*)*11 + 1, x_157);
lean_ctor_set_uint8(x_178, sizeof(void*)*11 + 2, x_158);
lean_ctor_set_uint8(x_178, sizeof(void*)*11 + 3, x_159);
lean_ctor_set_uint8(x_178, sizeof(void*)*11 + 4, x_160);
lean_inc_ref(x_178);
lean_inc_ref(x_150);
x_179 = l_Lean_Meta_Grind_setENode___redArg(x_150, x_178, x_6);
if (lean_obj_tag(x_179) == 0)
{
lean_dec_ref(x_179);
if (x_4 == 0)
{
lean_dec_ref(x_178);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_165 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
x_181 = lean_unsigned_to_nat(3u);
x_182 = l_Lean_Expr_isAppOfArity(x_150, x_180, x_181);
if (x_182 == 0)
{
lean_dec_ref(x_178);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_165 = lean_box(0);
goto block_172;
}
else
{
uint8_t x_183; 
x_183 = l_Lean_Meta_Grind_ENode_isCongrRoot(x_178);
lean_dec_ref(x_178);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_st_ref_get(x_6);
x_185 = lean_ctor_get(x_184, 2);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_184, 5);
lean_inc_ref(x_186);
lean_dec_ref(x_184);
lean_inc_ref(x_150);
x_187 = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(x_185, x_186, x_150);
if (lean_obj_tag(x_187) == 0)
{
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_165 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Lean_Meta_Grind_isFalseExpr___redArg(x_189, x_8);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_193 = lean_st_ref_take(x_6);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_193, 2);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_193, 3);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_193, 4);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_193, 5);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_193, 6);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_193, 7);
lean_inc_ref(x_201);
x_202 = lean_ctor_get_uint8(x_193, sizeof(void*)*17);
x_203 = lean_ctor_get(x_193, 8);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 9);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_193, 10);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_193, 11);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_193, 12);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_193, 13);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_193, 14);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_193, 15);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_193, 16);
lean_inc_ref(x_211);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 lean_ctor_release(x_193, 6);
 lean_ctor_release(x_193, 7);
 lean_ctor_release(x_193, 8);
 lean_ctor_release(x_193, 9);
 lean_ctor_release(x_193, 10);
 lean_ctor_release(x_193, 11);
 lean_ctor_release(x_193, 12);
 lean_ctor_release(x_193, 13);
 lean_ctor_release(x_193, 14);
 lean_ctor_release(x_193, 15);
 lean_ctor_release(x_193, 16);
 x_212 = x_193;
} else {
 lean_dec_ref(x_193);
 x_212 = lean_box(0);
}
x_213 = lean_box(0);
lean_inc_ref(x_150);
lean_inc_ref(x_196);
x_214 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3___redArg(x_196, x_199, x_150, x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 17, 1);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_194);
lean_ctor_set(x_215, 1, x_195);
lean_ctor_set(x_215, 2, x_196);
lean_ctor_set(x_215, 3, x_197);
lean_ctor_set(x_215, 4, x_198);
lean_ctor_set(x_215, 5, x_214);
lean_ctor_set(x_215, 6, x_200);
lean_ctor_set(x_215, 7, x_201);
lean_ctor_set(x_215, 8, x_203);
lean_ctor_set(x_215, 9, x_204);
lean_ctor_set(x_215, 10, x_205);
lean_ctor_set(x_215, 11, x_206);
lean_ctor_set(x_215, 12, x_207);
lean_ctor_set(x_215, 13, x_208);
lean_ctor_set(x_215, 14, x_209);
lean_ctor_set(x_215, 15, x_210);
lean_ctor_set(x_215, 16, x_211);
lean_ctor_set_uint8(x_215, sizeof(void*)*17, x_202);
x_216 = lean_st_ref_set(x_6, x_215);
lean_inc_ref(x_3);
lean_inc_ref(x_151);
lean_inc_ref_n(x_150, 2);
x_217 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_217, 0, x_150);
lean_ctor_set(x_217, 1, x_151);
lean_ctor_set(x_217, 2, x_3);
lean_ctor_set(x_217, 3, x_150);
lean_ctor_set(x_217, 4, x_153);
lean_ctor_set(x_217, 5, x_154);
lean_ctor_set(x_217, 6, x_156);
lean_ctor_set(x_217, 7, x_161);
lean_ctor_set(x_217, 8, x_162);
lean_ctor_set(x_217, 9, x_163);
lean_ctor_set(x_217, 10, x_164);
lean_ctor_set_uint8(x_217, sizeof(void*)*11, x_155);
lean_ctor_set_uint8(x_217, sizeof(void*)*11 + 1, x_157);
lean_ctor_set_uint8(x_217, sizeof(void*)*11 + 2, x_158);
lean_ctor_set_uint8(x_217, sizeof(void*)*11 + 3, x_159);
lean_ctor_set_uint8(x_217, sizeof(void*)*11 + 4, x_160);
lean_inc_ref(x_150);
x_218 = l_Lean_Meta_Grind_setENode___redArg(x_150, x_217, x_6);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_218);
x_219 = lean_st_ref_get(x_6);
lean_inc(x_189);
x_220 = l_Lean_Meta_Grind_Goal_getENode(x_219, x_189, x_12, x_13);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_221, 2);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_221, 4);
lean_inc(x_225);
x_226 = lean_ctor_get(x_221, 5);
lean_inc(x_226);
x_227 = lean_ctor_get_uint8(x_221, sizeof(void*)*11);
x_228 = lean_ctor_get(x_221, 6);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_221, sizeof(void*)*11 + 1);
x_230 = lean_ctor_get_uint8(x_221, sizeof(void*)*11 + 2);
x_231 = lean_ctor_get_uint8(x_221, sizeof(void*)*11 + 3);
x_232 = lean_ctor_get_uint8(x_221, sizeof(void*)*11 + 4);
x_233 = lean_ctor_get(x_221, 7);
lean_inc(x_233);
x_234 = lean_ctor_get(x_221, 8);
lean_inc(x_234);
x_235 = lean_ctor_get(x_221, 9);
lean_inc(x_235);
x_236 = lean_ctor_get(x_221, 10);
lean_inc(x_236);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 lean_ctor_release(x_221, 2);
 lean_ctor_release(x_221, 3);
 lean_ctor_release(x_221, 4);
 lean_ctor_release(x_221, 5);
 lean_ctor_release(x_221, 6);
 lean_ctor_release(x_221, 7);
 lean_ctor_release(x_221, 8);
 lean_ctor_release(x_221, 9);
 lean_ctor_release(x_221, 10);
 x_237 = x_221;
} else {
 lean_dec_ref(x_221);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 11, 5);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_222);
lean_ctor_set(x_238, 1, x_223);
lean_ctor_set(x_238, 2, x_224);
lean_ctor_set(x_238, 3, x_150);
lean_ctor_set(x_238, 4, x_225);
lean_ctor_set(x_238, 5, x_226);
lean_ctor_set(x_238, 6, x_228);
lean_ctor_set(x_238, 7, x_233);
lean_ctor_set(x_238, 8, x_234);
lean_ctor_set(x_238, 9, x_235);
lean_ctor_set(x_238, 10, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*11, x_227);
lean_ctor_set_uint8(x_238, sizeof(void*)*11 + 1, x_229);
lean_ctor_set_uint8(x_238, sizeof(void*)*11 + 2, x_230);
lean_ctor_set_uint8(x_238, sizeof(void*)*11 + 3, x_231);
lean_ctor_set_uint8(x_238, sizeof(void*)*11 + 4, x_232);
x_239 = l_Lean_Meta_Grind_setENode___redArg(x_189, x_238, x_6);
x_173 = x_239;
goto block_177;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_189);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_240 = lean_ctor_get(x_220, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_241 = x_220;
} else {
 lean_dec_ref(x_220);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
}
else
{
lean_dec(x_189);
lean_dec_ref(x_150);
x_173 = x_218;
goto block_177;
}
}
else
{
lean_dec(x_189);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_165 = lean_box(0);
goto block_172;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_189);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_243 = lean_ctor_get(x_190, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_244 = x_190;
} else {
 lean_dec_ref(x_190);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
return x_245;
}
}
}
else
{
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_165 = lean_box(0);
goto block_172;
}
}
}
}
else
{
lean_dec_ref(x_178);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec_ref(x_150);
x_173 = x_179;
goto block_177;
}
block_172:
{
uint8_t x_166; 
x_166 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_151, x_1);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_20);
lean_dec(x_16);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_17;
}
lean_ctor_set(x_167, 0, x_2);
lean_ctor_set(x_167, 1, x_151);
x_168 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(x_1, x_2, x_3, x_4, x_167, x_6, x_8, x_12, x_13);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_151);
lean_dec_ref(x_3);
lean_dec(x_2);
x_169 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
if (lean_is_scalar(x_17)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_17;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_16);
if (lean_is_scalar(x_20)) {
 x_171 = lean_alloc_ctor(0, 1, 0);
} else {
 x_171 = x_20;
}
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
block_177:
{
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_173);
x_165 = lean_box(0);
goto block_172;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec_ref(x_151);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
lean_dec(x_2);
x_246 = !lean_is_exclusive(x_18);
if (x_246 == 0)
{
return x_18;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_18, 0);
lean_inc(x_247);
lean_dec(x_18);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_isFalseExpr___redArg(x_2, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
lean_inc_ref(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_unbox(x_13);
lean_dec(x_13);
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8(x_1, x_14, x_2, x_16, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___redArg(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3_spec__5(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_propagateUp(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_16);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_propagateDown(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_16);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1;
x_2 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" new root ", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("adding ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ↦ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_233 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0;
x_422 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_233, x_16);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
x_424 = lean_unbox(x_423);
lean_dec(x_423);
if (x_424 == 0)
{
x_315 = x_10;
x_316 = x_11;
x_317 = x_12;
x_318 = x_13;
x_319 = x_14;
x_320 = x_15;
x_321 = x_16;
x_322 = x_17;
x_323 = lean_box(0);
goto block_421;
}
else
{
lean_object* x_425; 
x_425 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; 
lean_dec_ref(x_425);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_3);
x_426 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_10, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec_ref(x_426);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_4);
x_428 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_4, x_10, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
lean_dec_ref(x_428);
x_430 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6;
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_427);
x_432 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8;
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_429);
x_435 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_233, x_434, x_14, x_15, x_16, x_17);
lean_dec_ref(x_435);
x_315 = x_10;
x_316 = x_11;
x_317 = x_12;
x_318 = x_13;
x_319 = x_14;
x_320 = x_15;
x_321 = x_16;
x_322 = x_17;
x_323 = lean_box(0);
goto block_421;
}
else
{
uint8_t x_436; 
lean_dec(x_427);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_436 = !lean_is_exclusive(x_428);
if (x_436 == 0)
{
return x_428;
}
else
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_428, 0);
lean_inc(x_437);
lean_dec(x_428);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
return x_438;
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_439 = !lean_is_exclusive(x_426);
if (x_439 == 0)
{
return x_426;
}
else
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_426, 0);
lean_inc(x_440);
lean_dec(x_426);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
return x_441;
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_425;
}
}
block_57:
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_isInconsistent___redArg(x_24);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_33);
x_37 = l_Lean_Meta_Grind_ParentSet_elems(x_20);
lean_dec(x_20);
x_38 = lean_box(0);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_39 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_38, x_37, x_38, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_40 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_38, x_22, x_38, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_41 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(x_23, x_19, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
lean_dec_ref(x_19);
lean_dec_ref(x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec_ref(x_41);
x_42 = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(x_21, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
return x_42;
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
return x_41;
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_21);
lean_dec_ref(x_19);
return x_40;
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
return x_39;
}
}
else
{
lean_object* x_43; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
x_43 = lean_box(0);
lean_ctor_set(x_33, 0, x_43);
return x_33;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Meta_Grind_ParentSet_elems(x_20);
lean_dec(x_20);
x_47 = lean_box(0);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_48 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_47, x_46, x_47, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_48);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_49 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_47, x_22, x_47, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec_ref(x_49);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_50 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(x_23, x_19, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
lean_dec_ref(x_19);
lean_dec_ref(x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(x_21, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
return x_51;
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
return x_50;
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_21);
lean_dec_ref(x_19);
return x_49;
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
return x_48;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
x_54 = !lean_is_exclusive(x_33);
if (x_54 == 0)
{
return x_33;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_33, 0);
lean_inc(x_55);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
block_109:
{
lean_object* x_91; lean_object* x_92; 
lean_inc_ref(x_80);
x_91 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_60);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_78);
lean_ctor_set(x_91, 4, x_81);
lean_ctor_set(x_91, 5, x_89);
lean_ctor_set(x_91, 6, x_59);
lean_ctor_set(x_91, 7, x_72);
lean_ctor_set(x_91, 8, x_64);
lean_ctor_set(x_91, 9, x_68);
lean_ctor_set(x_91, 10, x_76);
lean_ctor_set_uint8(x_91, sizeof(void*)*11, x_84);
lean_ctor_set_uint8(x_91, sizeof(void*)*11 + 1, x_62);
lean_ctor_set_uint8(x_91, sizeof(void*)*11 + 2, x_86);
lean_ctor_set_uint8(x_91, sizeof(void*)*11 + 3, x_66);
lean_ctor_set_uint8(x_91, sizeof(void*)*11 + 4, x_90);
lean_inc_ref(x_82);
x_92 = l_Lean_Meta_Grind_setENode___redArg(x_82, x_91, x_61);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec_ref(x_92);
lean_inc(x_65);
lean_inc_ref(x_77);
lean_inc(x_69);
lean_inc_ref(x_73);
lean_inc(x_75);
lean_inc_ref(x_70);
lean_inc(x_74);
lean_inc(x_61);
lean_inc_ref(x_87);
x_93 = l_Lean_Meta_Grind_propagateBeta(x_87, x_63, x_61, x_74, x_70, x_75, x_73, x_69, x_77, x_65);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec_ref(x_93);
lean_inc(x_65);
lean_inc_ref(x_77);
lean_inc(x_69);
lean_inc_ref(x_73);
lean_inc(x_75);
lean_inc_ref(x_70);
lean_inc(x_74);
lean_inc(x_61);
lean_inc_ref(x_83);
x_94 = l_Lean_Meta_Grind_propagateBeta(x_83, x_79, x_61, x_74, x_70, x_75, x_73, x_69, x_77, x_65);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_dec_ref(x_94);
x_95 = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(x_8, x_7, x_61, x_77, x_65);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_Meta_Grind_resetParentsOf___redArg(x_71, x_61);
lean_dec_ref(x_71);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_dec_ref(x_97);
lean_inc(x_67);
x_98 = l_Lean_Meta_Grind_copyParentsTo(x_67, x_82, x_61, x_74, x_70, x_75, x_73, x_69, x_77, x_65);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_dec_ref(x_98);
x_99 = l_Lean_Meta_Grind_isInconsistent___redArg(x_61);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_80, x_61, x_74, x_70, x_75, x_73, x_69, x_77, x_65);
lean_dec_ref(x_80);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
x_19 = x_83;
x_20 = x_67;
x_21 = x_96;
x_22 = x_85;
x_23 = x_87;
x_24 = x_61;
x_25 = x_74;
x_26 = x_70;
x_27 = x_75;
x_28 = x_73;
x_29 = x_69;
x_30 = x_77;
x_31 = x_65;
x_32 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_96);
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
return x_102;
}
}
else
{
lean_dec_ref(x_80);
x_19 = x_83;
x_20 = x_67;
x_21 = x_96;
x_22 = x_85;
x_23 = x_87;
x_24 = x_61;
x_25 = x_74;
x_26 = x_70;
x_27 = x_75;
x_28 = x_73;
x_29 = x_69;
x_30 = x_77;
x_31 = x_65;
x_32 = lean_box(0);
goto block_57;
}
}
else
{
uint8_t x_103; 
lean_dec(x_96);
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
x_103 = !lean_is_exclusive(x_99);
if (x_103 == 0)
{
return x_99;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
lean_dec(x_96);
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
return x_98;
}
}
else
{
lean_dec(x_96);
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
return x_97;
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
x_106 = !lean_is_exclusive(x_95);
if (x_106 == 0)
{
return x_95;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
lean_dec(x_95);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_94;
}
}
else
{
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_61);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_93;
}
}
else
{
lean_dec_ref(x_87);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec_ref(x_63);
lean_dec(x_61);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_92;
}
}
block_144:
{
if (x_2 == 0)
{
if (x_142 == 0)
{
x_58 = lean_box(0);
x_59 = x_113;
x_60 = x_112;
x_61 = x_111;
x_62 = x_115;
x_63 = x_114;
x_64 = x_116;
x_65 = x_117;
x_66 = x_143;
x_67 = x_120;
x_68 = x_119;
x_69 = x_121;
x_70 = x_122;
x_71 = x_123;
x_72 = x_124;
x_73 = x_125;
x_74 = x_126;
x_75 = x_127;
x_76 = x_128;
x_77 = x_129;
x_78 = x_130;
x_79 = x_131;
x_80 = x_132;
x_81 = x_133;
x_82 = x_134;
x_83 = x_136;
x_84 = x_135;
x_85 = x_137;
x_86 = x_138;
x_87 = x_139;
x_88 = x_140;
x_89 = x_141;
x_90 = x_118;
goto block_109;
}
else
{
x_58 = lean_box(0);
x_59 = x_113;
x_60 = x_112;
x_61 = x_111;
x_62 = x_115;
x_63 = x_114;
x_64 = x_116;
x_65 = x_117;
x_66 = x_143;
x_67 = x_120;
x_68 = x_119;
x_69 = x_121;
x_70 = x_122;
x_71 = x_123;
x_72 = x_124;
x_73 = x_125;
x_74 = x_126;
x_75 = x_127;
x_76 = x_128;
x_77 = x_129;
x_78 = x_130;
x_79 = x_131;
x_80 = x_132;
x_81 = x_133;
x_82 = x_134;
x_83 = x_136;
x_84 = x_135;
x_85 = x_137;
x_86 = x_138;
x_87 = x_139;
x_88 = x_140;
x_89 = x_141;
x_90 = x_142;
goto block_109;
}
}
else
{
x_58 = lean_box(0);
x_59 = x_113;
x_60 = x_112;
x_61 = x_111;
x_62 = x_115;
x_63 = x_114;
x_64 = x_116;
x_65 = x_117;
x_66 = x_143;
x_67 = x_120;
x_68 = x_119;
x_69 = x_121;
x_70 = x_122;
x_71 = x_123;
x_72 = x_124;
x_73 = x_125;
x_74 = x_126;
x_75 = x_127;
x_76 = x_128;
x_77 = x_129;
x_78 = x_130;
x_79 = x_131;
x_80 = x_132;
x_81 = x_133;
x_82 = x_134;
x_83 = x_136;
x_84 = x_135;
x_85 = x_137;
x_86 = x_138;
x_87 = x_139;
x_88 = x_140;
x_89 = x_141;
x_90 = x_2;
goto block_109;
}
}
block_232:
{
lean_object* x_166; 
lean_inc(x_164);
lean_inc_ref(x_163);
lean_inc(x_162);
lean_inc_ref(x_161);
x_166 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_148, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_166);
x_167 = lean_st_ref_get(x_157);
x_168 = lean_st_ref_get(x_157);
lean_inc_ref(x_155);
x_169 = l_Lean_Meta_Grind_Goal_getENode(x_168, x_155, x_163, x_164);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_172 = lean_ctor_get(x_170, 1);
lean_dec(x_172);
x_173 = lean_ctor_get(x_8, 0);
x_174 = lean_ctor_get(x_8, 1);
x_175 = lean_ctor_get(x_8, 2);
x_176 = lean_ctor_get(x_8, 3);
x_177 = lean_ctor_get(x_8, 4);
x_178 = lean_ctor_get(x_8, 5);
x_179 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_180 = lean_ctor_get(x_8, 6);
x_181 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 1);
x_182 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 2);
x_183 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 3);
x_184 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 4);
x_185 = lean_ctor_get(x_8, 7);
x_186 = lean_ctor_get(x_8, 8);
x_187 = lean_ctor_get(x_8, 9);
x_188 = lean_ctor_get(x_8, 10);
lean_inc_ref(x_174);
lean_ctor_set(x_170, 1, x_174);
x_189 = l_Lean_Meta_Grind_setENode___redArg(x_149, x_170, x_157);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_189);
x_190 = 0;
x_191 = l_Lean_Meta_Grind_Goal_getEqc(x_167, x_3, x_190);
x_192 = lean_nat_add(x_180, x_156);
lean_dec(x_156);
if (x_183 == 0)
{
lean_inc(x_178);
lean_inc_ref(x_175);
lean_inc(x_177);
lean_inc_ref(x_173);
lean_inc_ref(x_176);
lean_inc(x_188);
lean_inc(x_185);
lean_inc(x_187);
lean_inc(x_186);
x_110 = lean_box(0);
x_111 = x_157;
x_112 = x_150;
x_113 = x_192;
x_114 = x_154;
x_115 = x_181;
x_116 = x_186;
x_117 = x_164;
x_118 = x_146;
x_119 = x_187;
x_120 = x_148;
x_121 = x_162;
x_122 = x_159;
x_123 = x_155;
x_124 = x_185;
x_125 = x_161;
x_126 = x_158;
x_127 = x_160;
x_128 = x_188;
x_129 = x_163;
x_130 = x_176;
x_131 = x_152;
x_132 = x_173;
x_133 = x_177;
x_134 = x_145;
x_135 = x_179;
x_136 = x_147;
x_137 = x_191;
x_138 = x_182;
x_139 = x_151;
x_140 = x_175;
x_141 = x_178;
x_142 = x_184;
x_143 = x_153;
goto block_144;
}
else
{
lean_inc(x_178);
lean_inc_ref(x_175);
lean_inc(x_177);
lean_inc_ref(x_173);
lean_inc_ref(x_176);
lean_inc(x_188);
lean_inc(x_185);
lean_inc(x_187);
lean_inc(x_186);
x_110 = lean_box(0);
x_111 = x_157;
x_112 = x_150;
x_113 = x_192;
x_114 = x_154;
x_115 = x_181;
x_116 = x_186;
x_117 = x_164;
x_118 = x_146;
x_119 = x_187;
x_120 = x_148;
x_121 = x_162;
x_122 = x_159;
x_123 = x_155;
x_124 = x_185;
x_125 = x_161;
x_126 = x_158;
x_127 = x_160;
x_128 = x_188;
x_129 = x_163;
x_130 = x_176;
x_131 = x_152;
x_132 = x_173;
x_133 = x_177;
x_134 = x_145;
x_135 = x_179;
x_136 = x_147;
x_137 = x_191;
x_138 = x_182;
x_139 = x_151;
x_140 = x_175;
x_141 = x_178;
x_142 = x_184;
x_143 = x_183;
goto block_144;
}
}
else
{
lean_dec_ref(x_167);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_189;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_193 = lean_ctor_get(x_170, 0);
x_194 = lean_ctor_get(x_170, 2);
x_195 = lean_ctor_get(x_170, 3);
x_196 = lean_ctor_get(x_170, 4);
x_197 = lean_ctor_get(x_170, 5);
x_198 = lean_ctor_get_uint8(x_170, sizeof(void*)*11);
x_199 = lean_ctor_get(x_170, 6);
x_200 = lean_ctor_get_uint8(x_170, sizeof(void*)*11 + 1);
x_201 = lean_ctor_get_uint8(x_170, sizeof(void*)*11 + 2);
x_202 = lean_ctor_get_uint8(x_170, sizeof(void*)*11 + 3);
x_203 = lean_ctor_get_uint8(x_170, sizeof(void*)*11 + 4);
x_204 = lean_ctor_get(x_170, 7);
x_205 = lean_ctor_get(x_170, 8);
x_206 = lean_ctor_get(x_170, 9);
x_207 = lean_ctor_get(x_170, 10);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_199);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_170);
x_208 = lean_ctor_get(x_8, 0);
x_209 = lean_ctor_get(x_8, 1);
x_210 = lean_ctor_get(x_8, 2);
x_211 = lean_ctor_get(x_8, 3);
x_212 = lean_ctor_get(x_8, 4);
x_213 = lean_ctor_get(x_8, 5);
x_214 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_215 = lean_ctor_get(x_8, 6);
x_216 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 1);
x_217 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 2);
x_218 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 3);
x_219 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 4);
x_220 = lean_ctor_get(x_8, 7);
x_221 = lean_ctor_get(x_8, 8);
x_222 = lean_ctor_get(x_8, 9);
x_223 = lean_ctor_get(x_8, 10);
lean_inc_ref(x_209);
x_224 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_224, 0, x_193);
lean_ctor_set(x_224, 1, x_209);
lean_ctor_set(x_224, 2, x_194);
lean_ctor_set(x_224, 3, x_195);
lean_ctor_set(x_224, 4, x_196);
lean_ctor_set(x_224, 5, x_197);
lean_ctor_set(x_224, 6, x_199);
lean_ctor_set(x_224, 7, x_204);
lean_ctor_set(x_224, 8, x_205);
lean_ctor_set(x_224, 9, x_206);
lean_ctor_set(x_224, 10, x_207);
lean_ctor_set_uint8(x_224, sizeof(void*)*11, x_198);
lean_ctor_set_uint8(x_224, sizeof(void*)*11 + 1, x_200);
lean_ctor_set_uint8(x_224, sizeof(void*)*11 + 2, x_201);
lean_ctor_set_uint8(x_224, sizeof(void*)*11 + 3, x_202);
lean_ctor_set_uint8(x_224, sizeof(void*)*11 + 4, x_203);
x_225 = l_Lean_Meta_Grind_setENode___redArg(x_149, x_224, x_157);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_225);
x_226 = 0;
x_227 = l_Lean_Meta_Grind_Goal_getEqc(x_167, x_3, x_226);
x_228 = lean_nat_add(x_215, x_156);
lean_dec(x_156);
if (x_218 == 0)
{
lean_inc(x_213);
lean_inc_ref(x_210);
lean_inc(x_212);
lean_inc_ref(x_208);
lean_inc_ref(x_211);
lean_inc(x_223);
lean_inc(x_220);
lean_inc(x_222);
lean_inc(x_221);
x_110 = lean_box(0);
x_111 = x_157;
x_112 = x_150;
x_113 = x_228;
x_114 = x_154;
x_115 = x_216;
x_116 = x_221;
x_117 = x_164;
x_118 = x_146;
x_119 = x_222;
x_120 = x_148;
x_121 = x_162;
x_122 = x_159;
x_123 = x_155;
x_124 = x_220;
x_125 = x_161;
x_126 = x_158;
x_127 = x_160;
x_128 = x_223;
x_129 = x_163;
x_130 = x_211;
x_131 = x_152;
x_132 = x_208;
x_133 = x_212;
x_134 = x_145;
x_135 = x_214;
x_136 = x_147;
x_137 = x_227;
x_138 = x_217;
x_139 = x_151;
x_140 = x_210;
x_141 = x_213;
x_142 = x_219;
x_143 = x_153;
goto block_144;
}
else
{
lean_inc(x_213);
lean_inc_ref(x_210);
lean_inc(x_212);
lean_inc_ref(x_208);
lean_inc_ref(x_211);
lean_inc(x_223);
lean_inc(x_220);
lean_inc(x_222);
lean_inc(x_221);
x_110 = lean_box(0);
x_111 = x_157;
x_112 = x_150;
x_113 = x_228;
x_114 = x_154;
x_115 = x_216;
x_116 = x_221;
x_117 = x_164;
x_118 = x_146;
x_119 = x_222;
x_120 = x_148;
x_121 = x_162;
x_122 = x_159;
x_123 = x_155;
x_124 = x_220;
x_125 = x_161;
x_126 = x_158;
x_127 = x_160;
x_128 = x_223;
x_129 = x_163;
x_130 = x_211;
x_131 = x_152;
x_132 = x_208;
x_133 = x_212;
x_134 = x_145;
x_135 = x_214;
x_136 = x_147;
x_137 = x_227;
x_138 = x_217;
x_139 = x_151;
x_140 = x_210;
x_141 = x_213;
x_142 = x_219;
x_143 = x_218;
goto block_144;
}
}
else
{
lean_dec_ref(x_167);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_225;
}
}
}
else
{
uint8_t x_229; 
lean_dec_ref(x_167);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_229 = !lean_is_exclusive(x_169);
if (x_229 == 0)
{
return x_169;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_169, 0);
lean_inc(x_230);
lean_dec(x_169);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
}
}
else
{
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec_ref(x_145);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_166;
}
}
block_292:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; 
x_248 = lean_ctor_get(x_7, 0);
x_249 = lean_ctor_get(x_7, 1);
x_250 = lean_ctor_get(x_7, 6);
x_251 = lean_ctor_get_uint8(x_7, sizeof(void*)*11 + 3);
x_252 = lean_ctor_get_uint8(x_7, sizeof(void*)*11 + 4);
x_253 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_248, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_255);
lean_dec_ref(x_6);
lean_inc_ref(x_255);
lean_inc_ref(x_3);
x_256 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_3, x_255, x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
lean_dec_ref(x_256);
x_257 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_233, x_245);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = lean_unbox(x_258);
lean_dec(x_258);
if (x_259 == 0)
{
lean_inc(x_250);
lean_inc_ref(x_248);
lean_inc_ref(x_249);
x_145 = x_255;
x_146 = x_252;
x_147 = x_234;
x_148 = x_254;
x_149 = x_235;
x_150 = x_249;
x_151 = x_236;
x_152 = x_238;
x_153 = x_251;
x_154 = x_237;
x_155 = x_248;
x_156 = x_250;
x_157 = x_239;
x_158 = x_240;
x_159 = x_241;
x_160 = x_242;
x_161 = x_243;
x_162 = x_244;
x_163 = x_245;
x_164 = x_246;
x_165 = lean_box(0);
goto block_232;
}
else
{
lean_object* x_260; 
x_260 = l_Lean_Meta_Grind_updateLastTag(x_239, x_240, x_241, x_242, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
lean_dec_ref(x_260);
lean_inc(x_246);
lean_inc_ref(x_245);
lean_inc(x_244);
lean_inc_ref(x_243);
lean_inc_ref(x_3);
x_261 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_239, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
lean_inc(x_246);
lean_inc_ref(x_245);
lean_inc(x_244);
lean_inc_ref(x_243);
lean_inc_ref(x_255);
x_263 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_255, x_239, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = lean_st_ref_get(x_239);
lean_inc_ref(x_3);
x_266 = l_Lean_Meta_Grind_Goal_getRoot(x_265, x_3, x_245, x_246);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
lean_inc(x_246);
lean_inc_ref(x_245);
lean_inc(x_244);
lean_inc_ref(x_243);
x_268 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_267, x_239, x_243, x_244, x_245, x_246);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
lean_dec_ref(x_268);
x_270 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2;
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_262);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
x_273 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_269);
x_276 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_233, x_275, x_243, x_244, x_245, x_246);
lean_dec_ref(x_276);
lean_inc(x_250);
lean_inc_ref(x_248);
lean_inc_ref(x_249);
x_145 = x_255;
x_146 = x_252;
x_147 = x_234;
x_148 = x_254;
x_149 = x_235;
x_150 = x_249;
x_151 = x_236;
x_152 = x_238;
x_153 = x_251;
x_154 = x_237;
x_155 = x_248;
x_156 = x_250;
x_157 = x_239;
x_158 = x_240;
x_159 = x_241;
x_160 = x_242;
x_161 = x_243;
x_162 = x_244;
x_163 = x_245;
x_164 = x_246;
x_165 = lean_box(0);
goto block_232;
}
else
{
uint8_t x_277; 
lean_dec(x_264);
lean_dec(x_262);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_277 = !lean_is_exclusive(x_268);
if (x_277 == 0)
{
return x_268;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_268, 0);
lean_inc(x_278);
lean_dec(x_268);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_264);
lean_dec(x_262);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_280 = !lean_is_exclusive(x_266);
if (x_280 == 0)
{
return x_266;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_266, 0);
lean_inc(x_281);
lean_dec(x_266);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_262);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_283 = !lean_is_exclusive(x_263);
if (x_283 == 0)
{
return x_263;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_263, 0);
lean_inc(x_284);
lean_dec(x_263);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
else
{
uint8_t x_286; 
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
x_286 = !lean_is_exclusive(x_261);
if (x_286 == 0)
{
return x_261;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_261, 0);
lean_inc(x_287);
lean_dec(x_261);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_260;
}
}
}
else
{
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_256;
}
}
else
{
uint8_t x_289; 
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_242);
lean_dec_ref(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec_ref(x_237);
lean_dec_ref(x_236);
lean_dec_ref(x_235);
lean_dec_ref(x_234);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_289 = !lean_is_exclusive(x_253);
if (x_289 == 0)
{
return x_253;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_253, 0);
lean_inc(x_290);
lean_dec(x_253);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
block_314:
{
uint8_t x_306; 
x_306 = l_Array_isEmpty___redArg(x_293);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_7, 0);
lean_inc(x_304);
lean_inc_ref(x_303);
lean_inc(x_302);
lean_inc_ref(x_301);
lean_inc(x_300);
lean_inc_ref(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc_ref(x_307);
x_308 = l_Lean_Meta_Grind_getFnRoots(x_307, x_297, x_298, x_299, x_300, x_301, x_302, x_303, x_304);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_234 = x_293;
x_235 = x_294;
x_236 = x_295;
x_237 = x_296;
x_238 = x_309;
x_239 = x_297;
x_240 = x_298;
x_241 = x_299;
x_242 = x_300;
x_243 = x_301;
x_244 = x_302;
x_245 = x_303;
x_246 = x_304;
x_247 = lean_box(0);
goto block_292;
}
else
{
uint8_t x_310; 
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec(x_302);
lean_dec_ref(x_301);
lean_dec(x_300);
lean_dec_ref(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_294);
lean_dec_ref(x_293);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_310 = !lean_is_exclusive(x_308);
if (x_310 == 0)
{
return x_308;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_308, 0);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; 
x_313 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_234 = x_293;
x_235 = x_294;
x_236 = x_295;
x_237 = x_296;
x_238 = x_313;
x_239 = x_297;
x_240 = x_298;
x_241 = x_299;
x_242 = x_300;
x_243 = x_301;
x_244 = x_302;
x_245 = x_303;
x_246 = x_304;
x_247 = lean_box(0);
goto block_292;
}
}
block_421:
{
lean_object* x_324; 
lean_inc_ref(x_3);
x_324 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(x_3, x_315, x_321, x_322);
if (lean_obj_tag(x_324) == 0)
{
uint8_t x_325; 
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_324, 0);
lean_dec(x_326);
x_327 = !lean_is_exclusive(x_5);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_328 = lean_ctor_get(x_5, 2);
x_329 = lean_ctor_get(x_5, 5);
lean_dec(x_329);
x_330 = lean_ctor_get(x_5, 4);
lean_dec(x_330);
lean_ctor_set_tag(x_324, 1);
lean_ctor_set(x_324, 0, x_4);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_1);
lean_inc_ref(x_328);
lean_ctor_set(x_5, 5, x_331);
lean_ctor_set(x_5, 4, x_324);
lean_ctor_set_uint8(x_5, sizeof(void*)*11, x_9);
lean_inc_ref(x_3);
x_332 = l_Lean_Meta_Grind_setENode___redArg(x_3, x_5, x_315);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; 
lean_dec_ref(x_332);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_333 = l_Lean_Meta_Grind_getEqcLambdas(x_7, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_dec_ref(x_333);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_335 = l_Lean_Meta_Grind_getEqcLambdas(x_8, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
x_337 = l_Array_isEmpty___redArg(x_334);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_8, 0);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc_ref(x_338);
x_339 = l_Lean_Meta_Grind_getFnRoots(x_338, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_293 = x_336;
x_294 = x_328;
x_295 = x_334;
x_296 = x_340;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
else
{
uint8_t x_341; 
lean_dec(x_336);
lean_dec(x_334);
lean_dec_ref(x_328);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_341 = !lean_is_exclusive(x_339);
if (x_341 == 0)
{
return x_339;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_339, 0);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_343, 0, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; 
x_344 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_293 = x_336;
x_294 = x_328;
x_295 = x_334;
x_296 = x_344;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
}
else
{
uint8_t x_345; 
lean_dec(x_334);
lean_dec_ref(x_328);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_345 = !lean_is_exclusive(x_335);
if (x_345 == 0)
{
return x_335;
}
else
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_335, 0);
lean_inc(x_346);
lean_dec(x_335);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
return x_347;
}
}
}
else
{
uint8_t x_348; 
lean_dec_ref(x_328);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_348 = !lean_is_exclusive(x_333);
if (x_348 == 0)
{
return x_333;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_333, 0);
lean_inc(x_349);
lean_dec(x_333);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
}
}
else
{
lean_dec_ref(x_328);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_332;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_351 = lean_ctor_get(x_5, 0);
x_352 = lean_ctor_get(x_5, 1);
x_353 = lean_ctor_get(x_5, 2);
x_354 = lean_ctor_get(x_5, 3);
x_355 = lean_ctor_get(x_5, 6);
x_356 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_357 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
x_358 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 3);
x_359 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 4);
x_360 = lean_ctor_get(x_5, 7);
x_361 = lean_ctor_get(x_5, 8);
x_362 = lean_ctor_get(x_5, 9);
x_363 = lean_ctor_get(x_5, 10);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_5);
lean_ctor_set_tag(x_324, 1);
lean_ctor_set(x_324, 0, x_4);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_1);
lean_inc_ref(x_353);
x_365 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_365, 0, x_351);
lean_ctor_set(x_365, 1, x_352);
lean_ctor_set(x_365, 2, x_353);
lean_ctor_set(x_365, 3, x_354);
lean_ctor_set(x_365, 4, x_324);
lean_ctor_set(x_365, 5, x_364);
lean_ctor_set(x_365, 6, x_355);
lean_ctor_set(x_365, 7, x_360);
lean_ctor_set(x_365, 8, x_361);
lean_ctor_set(x_365, 9, x_362);
lean_ctor_set(x_365, 10, x_363);
lean_ctor_set_uint8(x_365, sizeof(void*)*11, x_9);
lean_ctor_set_uint8(x_365, sizeof(void*)*11 + 1, x_356);
lean_ctor_set_uint8(x_365, sizeof(void*)*11 + 2, x_357);
lean_ctor_set_uint8(x_365, sizeof(void*)*11 + 3, x_358);
lean_ctor_set_uint8(x_365, sizeof(void*)*11 + 4, x_359);
lean_inc_ref(x_3);
x_366 = l_Lean_Meta_Grind_setENode___redArg(x_3, x_365, x_315);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
lean_dec_ref(x_366);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_367 = l_Lean_Meta_Grind_getEqcLambdas(x_7, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_369 = l_Lean_Meta_Grind_getEqcLambdas(x_8, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; uint8_t x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec_ref(x_369);
x_371 = l_Array_isEmpty___redArg(x_368);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_8, 0);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc_ref(x_372);
x_373 = l_Lean_Meta_Grind_getFnRoots(x_372, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec_ref(x_373);
x_293 = x_370;
x_294 = x_353;
x_295 = x_368;
x_296 = x_374;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_370);
lean_dec(x_368);
lean_dec_ref(x_353);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 1, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_375);
return x_377;
}
}
else
{
lean_object* x_378; 
x_378 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_293 = x_370;
x_294 = x_353;
x_295 = x_368;
x_296 = x_378;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_368);
lean_dec_ref(x_353);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_379 = lean_ctor_get(x_369, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_380 = x_369;
} else {
 lean_dec_ref(x_369);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec_ref(x_353);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_382 = lean_ctor_get(x_367, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_383 = x_367;
} else {
 lean_dec_ref(x_367);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_382);
return x_384;
}
}
else
{
lean_dec_ref(x_353);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_366;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_324);
x_385 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_385);
x_386 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_386);
x_387 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_387);
x_388 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_388);
x_389 = lean_ctor_get(x_5, 6);
lean_inc(x_389);
x_390 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_391 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
x_392 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 3);
x_393 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 4);
x_394 = lean_ctor_get(x_5, 7);
lean_inc(x_394);
x_395 = lean_ctor_get(x_5, 8);
lean_inc(x_395);
x_396 = lean_ctor_get(x_5, 9);
lean_inc(x_396);
x_397 = lean_ctor_get(x_5, 10);
lean_inc(x_397);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 lean_ctor_release(x_5, 10);
 x_398 = x_5;
} else {
 lean_dec_ref(x_5);
 x_398 = lean_box(0);
}
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_4);
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_1);
lean_inc_ref(x_387);
if (lean_is_scalar(x_398)) {
 x_401 = lean_alloc_ctor(0, 11, 5);
} else {
 x_401 = x_398;
}
lean_ctor_set(x_401, 0, x_385);
lean_ctor_set(x_401, 1, x_386);
lean_ctor_set(x_401, 2, x_387);
lean_ctor_set(x_401, 3, x_388);
lean_ctor_set(x_401, 4, x_399);
lean_ctor_set(x_401, 5, x_400);
lean_ctor_set(x_401, 6, x_389);
lean_ctor_set(x_401, 7, x_394);
lean_ctor_set(x_401, 8, x_395);
lean_ctor_set(x_401, 9, x_396);
lean_ctor_set(x_401, 10, x_397);
lean_ctor_set_uint8(x_401, sizeof(void*)*11, x_9);
lean_ctor_set_uint8(x_401, sizeof(void*)*11 + 1, x_390);
lean_ctor_set_uint8(x_401, sizeof(void*)*11 + 2, x_391);
lean_ctor_set_uint8(x_401, sizeof(void*)*11 + 3, x_392);
lean_ctor_set_uint8(x_401, sizeof(void*)*11 + 4, x_393);
lean_inc_ref(x_3);
x_402 = l_Lean_Meta_Grind_setENode___redArg(x_3, x_401, x_315);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
lean_dec_ref(x_402);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_403 = l_Lean_Meta_Grind_getEqcLambdas(x_7, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec_ref(x_403);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
x_405 = l_Lean_Meta_Grind_getEqcLambdas(x_8, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec_ref(x_405);
x_407 = l_Array_isEmpty___redArg(x_404);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_8, 0);
lean_inc(x_322);
lean_inc_ref(x_321);
lean_inc(x_320);
lean_inc_ref(x_319);
lean_inc(x_318);
lean_inc_ref(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc_ref(x_408);
x_409 = l_Lean_Meta_Grind_getFnRoots(x_408, x_315, x_316, x_317, x_318, x_319, x_320, x_321, x_322);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec_ref(x_409);
x_293 = x_406;
x_294 = x_387;
x_295 = x_404;
x_296 = x_410;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_406);
lean_dec(x_404);
lean_dec_ref(x_387);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 1, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_411);
return x_413;
}
}
else
{
lean_object* x_414; 
x_414 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0;
x_293 = x_406;
x_294 = x_387;
x_295 = x_404;
x_296 = x_414;
x_297 = x_315;
x_298 = x_316;
x_299 = x_317;
x_300 = x_318;
x_301 = x_319;
x_302 = x_320;
x_303 = x_321;
x_304 = x_322;
x_305 = lean_box(0);
goto block_314;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_404);
lean_dec_ref(x_387);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_415 = lean_ctor_get(x_405, 0);
lean_inc(x_415);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 x_416 = x_405;
} else {
 lean_dec_ref(x_405);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 1, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec_ref(x_387);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_418 = lean_ctor_get(x_403, 0);
lean_inc(x_418);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_419 = x_403;
} else {
 lean_dec_ref(x_403);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 1, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_418);
return x_420;
}
}
else
{
lean_dec_ref(x_387);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_402;
}
}
}
else
{
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_324;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_2);
x_20 = lean_unbox(x_9);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after addEqStep, ", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqc", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2;
x_2 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" are already in the same equivalence class", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_19; 
x_18 = lean_st_ref_get(x_5);
lean_inc_ref(x_1);
x_19 = l_Lean_Meta_Grind_Goal_getENode(x_18, x_1, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_st_ref_get(x_5);
lean_inc_ref(x_2);
x_22 = l_Lean_Meta_Grind_Goal_getENode(x_21, x_2, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_23, 2);
x_26 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_113; uint8_t x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_287; lean_object* x_288; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_287 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3;
x_296 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_287, x_11);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_dec_ref(x_296);
x_298 = lean_unbox(x_297);
lean_dec(x_297);
if (x_298 == 0)
{
x_262 = x_5;
x_263 = x_6;
x_264 = x_7;
x_265 = x_8;
x_266 = x_9;
x_267 = x_10;
x_268 = x_11;
x_269 = x_12;
x_270 = lean_box(0);
goto block_286;
}
else
{
lean_object* x_299; 
x_299 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_299) == 0)
{
lean_dec_ref(x_299);
if (x_4 == 0)
{
lean_object* x_300; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_300 = l_Lean_Meta_mkEq(x_1, x_2, x_9, x_10, x_11, x_12);
x_288 = x_300;
goto block_295;
}
else
{
lean_object* x_301; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_301 = l_Lean_Meta_mkHEq(x_1, x_2, x_9, x_10, x_11, x_12);
x_288 = x_301;
goto block_295;
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_299;
}
}
block_52:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0;
x_37 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_36, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Grind_checkInvariants(x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Grind_updateLastTag(x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
x_42 = lean_st_ref_get(x_27);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_43 = l_Lean_Meta_Grind_Goal_ppState(x_42, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_36, x_46, x_31, x_32, x_33, x_34);
lean_dec_ref(x_47);
x_48 = l_Lean_Meta_Grind_checkInvariants(x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_27);
return x_41;
}
}
}
block_74:
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Grind_isInconsistent___redArg(x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
if (x_54 == 0)
{
lean_dec_ref(x_55);
lean_dec_ref(x_53);
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_60;
x_32 = x_61;
x_33 = x_62;
x_34 = x_63;
x_35 = lean_box(0);
goto block_52;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_68);
lean_dec_ref(x_55);
x_69 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_69);
lean_dec_ref(x_53);
lean_inc(x_63);
lean_inc_ref(x_62);
lean_inc(x_61);
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_70 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(x_68, x_69, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_60;
x_32 = x_61;
x_33 = x_62;
x_34 = x_63;
x_35 = lean_box(0);
goto block_52;
}
else
{
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
return x_70;
}
}
}
else
{
lean_dec_ref(x_55);
lean_dec_ref(x_53);
x_27 = x_56;
x_28 = x_57;
x_29 = x_58;
x_30 = x_59;
x_31 = x_60;
x_32 = x_61;
x_33 = x_62;
x_34 = x_63;
x_35 = lean_box(0);
goto block_52;
}
}
else
{
uint8_t x_71; 
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec_ref(x_53);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
block_91:
{
if (x_87 == 0)
{
x_53 = x_75;
x_54 = x_77;
x_55 = x_82;
x_56 = x_86;
x_57 = x_80;
x_58 = x_76;
x_59 = x_84;
x_60 = x_79;
x_61 = x_78;
x_62 = x_81;
x_63 = x_85;
x_64 = lean_box(0);
goto block_74;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
lean_inc_ref(x_81);
lean_inc(x_78);
lean_inc_ref(x_79);
lean_inc(x_84);
lean_inc_ref(x_76);
lean_inc(x_80);
lean_inc(x_86);
lean_inc_ref(x_89);
lean_inc_ref(x_88);
x_90 = l_Lean_Meta_Grind_propagateCtor(x_88, x_89, x_86, x_80, x_76, x_84, x_79, x_78, x_81, x_85);
if (lean_obj_tag(x_90) == 0)
{
lean_dec_ref(x_90);
x_53 = x_75;
x_54 = x_77;
x_55 = x_82;
x_56 = x_86;
x_57 = x_80;
x_58 = x_76;
x_59 = x_84;
x_60 = x_79;
x_61 = x_78;
x_62 = x_81;
x_63 = x_85;
x_64 = lean_box(0);
goto block_74;
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec_ref(x_75);
return x_90;
}
}
}
block_112:
{
lean_object* x_104; 
x_104 = l_Lean_Meta_Grind_isInconsistent___redArg(x_95);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_94, sizeof(void*)*11 + 2);
if (x_107 == 0)
{
x_75 = x_92;
x_76 = x_97;
x_77 = x_93;
x_78 = x_100;
x_79 = x_99;
x_80 = x_96;
x_81 = x_101;
x_82 = x_94;
x_83 = lean_box(0);
x_84 = x_98;
x_85 = x_102;
x_86 = x_95;
x_87 = x_26;
goto block_91;
}
else
{
uint8_t x_108; 
x_108 = lean_ctor_get_uint8(x_92, sizeof(void*)*11 + 2);
x_75 = x_92;
x_76 = x_97;
x_77 = x_93;
x_78 = x_100;
x_79 = x_99;
x_80 = x_96;
x_81 = x_101;
x_82 = x_94;
x_83 = lean_box(0);
x_84 = x_98;
x_85 = x_102;
x_86 = x_95;
x_87 = x_108;
goto block_91;
}
}
else
{
x_53 = x_92;
x_54 = x_93;
x_55 = x_94;
x_56 = x_95;
x_57 = x_96;
x_58 = x_97;
x_59 = x_98;
x_60 = x_99;
x_61 = x_100;
x_62 = x_101;
x_63 = x_102;
x_64 = lean_box(0);
goto block_74;
}
}
else
{
uint8_t x_109; 
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_92);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
block_127:
{
if (x_116 == 0)
{
x_92 = x_113;
x_93 = x_114;
x_94 = x_115;
x_95 = x_117;
x_96 = x_118;
x_97 = x_119;
x_98 = x_120;
x_99 = x_121;
x_100 = x_122;
x_101 = x_123;
x_102 = x_124;
x_103 = lean_box(0);
goto block_112;
}
else
{
lean_object* x_126; 
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_118);
lean_inc(x_117);
x_126 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(x_117, x_118, x_119, x_120, x_121, x_122, x_123, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_126);
x_92 = x_113;
x_93 = x_114;
x_94 = x_115;
x_95 = x_117;
x_96 = x_118;
x_97 = x_119;
x_98 = x_120;
x_99 = x_121;
x_100 = x_122;
x_101 = x_123;
x_102 = x_124;
x_103 = lean_box(0);
goto block_112;
}
else
{
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec_ref(x_113);
return x_126;
}
}
}
block_143:
{
uint8_t x_141; lean_object* x_142; 
x_141 = 1;
lean_inc(x_130);
lean_inc_ref(x_138);
lean_inc(x_140);
lean_inc_ref(x_137);
lean_inc(x_133);
lean_inc_ref(x_129);
lean_inc(x_139);
lean_inc(x_136);
lean_inc_ref(x_131);
lean_inc_ref(x_128);
x_142 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_2, x_1, x_23, x_20, x_128, x_131, x_141, x_136, x_139, x_129, x_133, x_137, x_140, x_138, x_130);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
x_113 = x_128;
x_114 = x_134;
x_115 = x_131;
x_116 = x_132;
x_117 = x_136;
x_118 = x_139;
x_119 = x_129;
x_120 = x_133;
x_121 = x_137;
x_122 = x_140;
x_123 = x_138;
x_124 = x_130;
x_125 = lean_box(0);
goto block_127;
}
else
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec(x_133);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_128);
return x_142;
}
}
block_158:
{
lean_object* x_157; 
lean_inc(x_146);
lean_inc_ref(x_154);
lean_inc(x_156);
lean_inc_ref(x_153);
lean_inc(x_149);
lean_inc_ref(x_145);
lean_inc(x_155);
lean_inc(x_152);
lean_inc_ref(x_144);
lean_inc_ref(x_147);
x_157 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_1, x_2, x_20, x_23, x_147, x_144, x_26, x_152, x_155, x_145, x_149, x_153, x_156, x_154, x_146);
if (lean_obj_tag(x_157) == 0)
{
lean_dec_ref(x_157);
x_113 = x_144;
x_114 = x_150;
x_115 = x_147;
x_116 = x_148;
x_117 = x_152;
x_118 = x_155;
x_119 = x_145;
x_120 = x_149;
x_121 = x_153;
x_122 = x_156;
x_123 = x_154;
x_124 = x_146;
x_125 = lean_box(0);
goto block_127;
}
else
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec(x_149);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
return x_157;
}
}
block_173:
{
if (x_172 == 0)
{
x_144 = x_159;
x_145 = x_160;
x_146 = x_161;
x_147 = x_162;
x_148 = x_163;
x_149 = x_164;
x_150 = x_165;
x_151 = lean_box(0);
x_152 = x_167;
x_153 = x_168;
x_154 = x_169;
x_155 = x_170;
x_156 = x_171;
goto block_158;
}
else
{
x_128 = x_159;
x_129 = x_160;
x_130 = x_161;
x_131 = x_162;
x_132 = x_163;
x_133 = x_164;
x_134 = x_165;
x_135 = lean_box(0);
x_136 = x_167;
x_137 = x_168;
x_138 = x_169;
x_139 = x_170;
x_140 = x_171;
goto block_143;
}
}
block_192:
{
uint8_t x_191; 
x_191 = lean_nat_dec_lt(x_175, x_181);
lean_dec(x_181);
lean_dec(x_175);
if (x_191 == 0)
{
x_159 = x_174;
x_160 = x_178;
x_161 = x_179;
x_162 = x_180;
x_163 = x_182;
x_164 = x_183;
x_165 = x_184;
x_166 = lean_box(0);
x_167 = x_186;
x_168 = x_187;
x_169 = x_188;
x_170 = x_189;
x_171 = x_190;
x_172 = x_26;
goto block_173;
}
else
{
if (x_176 == 0)
{
if (x_191 == 0)
{
x_159 = x_174;
x_160 = x_178;
x_161 = x_179;
x_162 = x_180;
x_163 = x_182;
x_164 = x_183;
x_165 = x_184;
x_166 = lean_box(0);
x_167 = x_186;
x_168 = x_187;
x_169 = x_188;
x_170 = x_189;
x_171 = x_190;
x_172 = x_26;
goto block_173;
}
else
{
if (x_177 == 0)
{
x_159 = x_174;
x_160 = x_178;
x_161 = x_179;
x_162 = x_180;
x_163 = x_182;
x_164 = x_183;
x_165 = x_184;
x_166 = lean_box(0);
x_167 = x_186;
x_168 = x_187;
x_169 = x_188;
x_170 = x_189;
x_171 = x_190;
x_172 = x_191;
goto block_173;
}
else
{
x_144 = x_174;
x_145 = x_178;
x_146 = x_179;
x_147 = x_180;
x_148 = x_182;
x_149 = x_183;
x_150 = x_184;
x_151 = lean_box(0);
x_152 = x_186;
x_153 = x_187;
x_154 = x_188;
x_155 = x_189;
x_156 = x_190;
goto block_158;
}
}
}
else
{
x_159 = x_174;
x_160 = x_178;
x_161 = x_179;
x_162 = x_180;
x_163 = x_182;
x_164 = x_183;
x_165 = x_184;
x_166 = lean_box(0);
x_167 = x_186;
x_168 = x_187;
x_169 = x_188;
x_170 = x_189;
x_171 = x_190;
x_172 = x_26;
goto block_173;
}
}
}
block_216:
{
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_196, sizeof(void*)*11 + 2);
if (x_207 == 0)
{
if (x_26 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_196, 6);
lean_inc(x_208);
x_209 = lean_ctor_get(x_193, 6);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_193, sizeof(void*)*11 + 1);
x_211 = lean_ctor_get_uint8(x_193, sizeof(void*)*11 + 2);
x_174 = x_193;
x_175 = x_209;
x_176 = x_210;
x_177 = x_211;
x_178 = x_194;
x_179 = x_195;
x_180 = x_196;
x_181 = x_208;
x_182 = x_197;
x_183 = x_198;
x_184 = x_199;
x_185 = lean_box(0);
x_186 = x_201;
x_187 = x_202;
x_188 = x_203;
x_189 = x_204;
x_190 = x_205;
goto block_192;
}
else
{
x_128 = x_193;
x_129 = x_194;
x_130 = x_195;
x_131 = x_196;
x_132 = x_197;
x_133 = x_198;
x_134 = x_199;
x_135 = lean_box(0);
x_136 = x_201;
x_137 = x_202;
x_138 = x_203;
x_139 = x_204;
x_140 = x_205;
goto block_143;
}
}
else
{
uint8_t x_212; 
x_212 = lean_ctor_get_uint8(x_193, sizeof(void*)*11 + 2);
if (x_212 == 0)
{
x_128 = x_193;
x_129 = x_194;
x_130 = x_195;
x_131 = x_196;
x_132 = x_197;
x_133 = x_198;
x_134 = x_199;
x_135 = lean_box(0);
x_136 = x_201;
x_137 = x_202;
x_138 = x_203;
x_139 = x_204;
x_140 = x_205;
goto block_143;
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_ctor_get(x_196, 6);
lean_inc(x_213);
x_214 = lean_ctor_get(x_193, 6);
lean_inc(x_214);
x_215 = lean_ctor_get_uint8(x_193, sizeof(void*)*11 + 1);
x_174 = x_193;
x_175 = x_214;
x_176 = x_215;
x_177 = x_212;
x_178 = x_194;
x_179 = x_195;
x_180 = x_196;
x_181 = x_213;
x_182 = x_197;
x_183 = x_198;
x_184 = x_199;
x_185 = lean_box(0);
x_186 = x_201;
x_187 = x_202;
x_188 = x_203;
x_189 = x_204;
x_190 = x_205;
goto block_192;
}
}
}
else
{
x_128 = x_193;
x_129 = x_194;
x_130 = x_195;
x_131 = x_196;
x_132 = x_197;
x_133 = x_198;
x_134 = x_199;
x_135 = lean_box(0);
x_136 = x_201;
x_137 = x_202;
x_138 = x_203;
x_139 = x_204;
x_140 = x_205;
goto block_143;
}
}
block_232:
{
uint8_t x_230; 
x_230 = lean_ctor_get_uint8(x_218, sizeof(void*)*11 + 1);
if (x_230 == 0)
{
x_193 = x_217;
x_194 = x_223;
x_195 = x_228;
x_196 = x_218;
x_197 = x_219;
x_198 = x_224;
x_199 = x_220;
x_200 = lean_box(0);
x_201 = x_221;
x_202 = x_225;
x_203 = x_227;
x_204 = x_222;
x_205 = x_226;
x_206 = x_26;
goto block_216;
}
else
{
uint8_t x_231; 
x_231 = lean_ctor_get_uint8(x_217, sizeof(void*)*11 + 1);
if (x_231 == 0)
{
x_128 = x_217;
x_129 = x_223;
x_130 = x_228;
x_131 = x_218;
x_132 = x_219;
x_133 = x_224;
x_134 = x_220;
x_135 = lean_box(0);
x_136 = x_221;
x_137 = x_225;
x_138 = x_227;
x_139 = x_222;
x_140 = x_226;
goto block_143;
}
else
{
x_193 = x_217;
x_194 = x_223;
x_195 = x_228;
x_196 = x_218;
x_197 = x_219;
x_198 = x_224;
x_199 = x_220;
x_200 = lean_box(0);
x_201 = x_221;
x_202 = x_225;
x_203 = x_227;
x_204 = x_222;
x_205 = x_226;
x_206 = x_26;
goto block_216;
}
}
}
block_246:
{
lean_object* x_245; 
x_245 = l_Lean_Meta_Grind_markAsInconsistent___redArg(x_236, x_239, x_243, x_235, x_241);
if (lean_obj_tag(x_245) == 0)
{
lean_dec_ref(x_245);
x_217 = x_233;
x_218 = x_240;
x_219 = x_238;
x_220 = x_26;
x_221 = x_236;
x_222 = x_234;
x_223 = x_244;
x_224 = x_237;
x_225 = x_239;
x_226 = x_243;
x_227 = x_235;
x_228 = x_241;
x_229 = lean_box(0);
goto block_232;
}
else
{
lean_dec_ref(x_244);
lean_dec(x_243);
lean_dec(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_239);
lean_dec(x_237);
lean_dec(x_236);
lean_dec_ref(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_245;
}
}
block_261:
{
if (x_258 == 0)
{
x_217 = x_247;
x_218 = x_253;
x_219 = x_26;
x_220 = x_26;
x_221 = x_250;
x_222 = x_249;
x_223 = x_257;
x_224 = x_251;
x_225 = x_252;
x_226 = x_256;
x_227 = x_248;
x_228 = x_254;
x_229 = lean_box(0);
goto block_232;
}
else
{
uint8_t x_259; 
lean_inc_ref(x_24);
x_259 = l_Lean_Expr_isTrue(x_24);
if (x_259 == 0)
{
uint8_t x_260; 
lean_inc_ref(x_25);
x_260 = l_Lean_Expr_isTrue(x_25);
if (x_260 == 0)
{
x_217 = x_247;
x_218 = x_253;
x_219 = x_26;
x_220 = x_258;
x_221 = x_250;
x_222 = x_249;
x_223 = x_257;
x_224 = x_251;
x_225 = x_252;
x_226 = x_256;
x_227 = x_248;
x_228 = x_254;
x_229 = lean_box(0);
goto block_232;
}
else
{
x_233 = x_247;
x_234 = x_249;
x_235 = x_248;
x_236 = x_250;
x_237 = x_251;
x_238 = x_258;
x_239 = x_252;
x_240 = x_253;
x_241 = x_254;
x_242 = lean_box(0);
x_243 = x_256;
x_244 = x_257;
goto block_246;
}
}
else
{
x_233 = x_247;
x_234 = x_249;
x_235 = x_248;
x_236 = x_250;
x_237 = x_251;
x_238 = x_258;
x_239 = x_252;
x_240 = x_253;
x_241 = x_254;
x_242 = lean_box(0);
x_243 = x_256;
x_244 = x_257;
goto block_246;
}
}
}
block_286:
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_st_ref_get(x_262);
lean_inc_ref(x_24);
x_272 = l_Lean_Meta_Grind_Goal_getENode(x_271, x_24, x_268, x_269);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
x_274 = lean_st_ref_get(x_262);
lean_inc_ref(x_25);
x_275 = l_Lean_Meta_Grind_Goal_getENode(x_274, x_25, x_268, x_269);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
x_276 = lean_ctor_get_uint8(x_273, sizeof(void*)*11 + 1);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
lean_dec_ref(x_275);
x_247 = x_277;
x_248 = x_268;
x_249 = x_263;
x_250 = x_262;
x_251 = x_265;
x_252 = x_266;
x_253 = x_273;
x_254 = x_269;
x_255 = lean_box(0);
x_256 = x_267;
x_257 = x_264;
x_258 = x_26;
goto block_261;
}
else
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
lean_dec_ref(x_275);
x_279 = lean_ctor_get_uint8(x_278, sizeof(void*)*11 + 1);
x_247 = x_278;
x_248 = x_268;
x_249 = x_263;
x_250 = x_262;
x_251 = x_265;
x_252 = x_266;
x_253 = x_273;
x_254 = x_269;
x_255 = lean_box(0);
x_256 = x_267;
x_257 = x_264;
x_258 = x_279;
goto block_261;
}
}
else
{
uint8_t x_280; 
lean_dec(x_273);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_280 = !lean_is_exclusive(x_275);
if (x_280 == 0)
{
return x_275;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
lean_dec(x_275);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_283 = !lean_is_exclusive(x_272);
if (x_283 == 0)
{
return x_272;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_272, 0);
lean_inc(x_284);
lean_dec(x_272);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
block_295:
{
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = l_Lean_MessageData_ofExpr(x_289);
x_291 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_287, x_290, x_9, x_10, x_11, x_12);
lean_dec_ref(x_291);
x_262 = x_5;
x_263 = x_6;
x_264 = x_7;
x_265 = x_8;
x_266 = x_9;
x_267 = x_10;
x_268 = x_11;
x_269 = x_12;
x_270 = lean_box(0);
goto block_286;
}
else
{
uint8_t x_292; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_288);
if (x_292 == 0)
{
return x_288;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_288, 0);
lean_inc(x_293);
lean_dec(x_288);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_3);
x_302 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0;
x_303 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_302, x_11);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec_ref(x_303);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_306; 
x_306 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
lean_dec_ref(x_306);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_307 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_1, x_5, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_309 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_2, x_5, x_9, x_10, x_11, x_12);
lean_dec(x_5);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
x_311 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5;
x_312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_312, 0, x_308);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_310);
x_314 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7;
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_302, x_315, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_316);
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_317; 
lean_dec(x_308);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_317 = !lean_is_exclusive(x_309);
if (x_317 == 0)
{
return x_309;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_309, 0);
lean_inc(x_318);
lean_dec(x_309);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_2);
x_320 = !lean_is_exclusive(x_307);
if (x_320 == 0)
{
return x_307;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_307, 0);
lean_inc(x_321);
lean_dec(x_307);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
return x_322;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_306;
}
}
}
}
else
{
uint8_t x_323; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_323 = !lean_is_exclusive(x_22);
if (x_323 == 0)
{
return x_22;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_22, 0);
lean_inc(x_324);
lean_dec(x_22);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
return x_325;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_326 = !lean_is_exclusive(x_19);
if (x_326 == 0)
{
return x_19;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_19, 0);
lean_inc(x_327);
lean_dec(x_19);
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_327);
return x_328;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 7);
lean_dec(x_5);
x_6 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0;
lean_ctor_set(x_3, 7, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*17);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get(x_3, 11);
x_22 = lean_ctor_get(x_3, 12);
x_23 = lean_ctor_get(x_3, 13);
x_24 = lean_ctor_get(x_3, 14);
x_25 = lean_ctor_get(x_3, 15);
x_26 = lean_ctor_get(x_3, 16);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_27 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0;
x_28 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set(x_28, 3, x_13);
lean_ctor_set(x_28, 4, x_14);
lean_ctor_set(x_28, 5, x_15);
lean_ctor_set(x_28, 6, x_16);
lean_ctor_set(x_28, 7, x_27);
lean_ctor_set(x_28, 8, x_18);
lean_ctor_set(x_28, 9, x_19);
lean_ctor_set(x_28, 10, x_20);
lean_ctor_set(x_28, 11, x_21);
lean_ctor_set(x_28, 12, x_22);
lean_ctor_set(x_28, 13, x_23);
lean_ctor_set(x_28, 14, x_24);
lean_ctor_set(x_28, 15, x_25);
lean_ctor_set(x_28, 16, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*17, x_17);
x_29 = lean_st_ref_set(x_1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Array_back_x3f___redArg(x_4);
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_take(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = lean_array_pop(x_9);
lean_ctor_set(x_7, 7, x_10);
x_11 = lean_st_ref_set(x_1, x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = lean_ctor_get(x_7, 4);
x_18 = lean_ctor_get(x_7, 5);
x_19 = lean_ctor_get(x_7, 6);
x_20 = lean_ctor_get(x_7, 7);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*17);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get(x_7, 12);
x_27 = lean_ctor_get(x_7, 13);
x_28 = lean_ctor_get(x_7, 14);
x_29 = lean_ctor_get(x_7, 15);
x_30 = lean_ctor_get(x_7, 16);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_31 = lean_array_pop(x_20);
x_32 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_15);
lean_ctor_set(x_32, 3, x_16);
lean_ctor_set(x_32, 4, x_17);
lean_ctor_set(x_32, 5, x_18);
lean_ctor_set(x_32, 6, x_19);
lean_ctor_set(x_32, 7, x_31);
lean_ctor_set(x_32, 8, x_22);
lean_ctor_set(x_32, 9, x_23);
lean_ctor_set(x_32, 10, x_24);
lean_ctor_set(x_32, 11, x_25);
lean_ctor_set(x_32, 12, x_26);
lean_ctor_set(x_32, 13, x_27);
lean_ctor_set(x_32, 14, x_28);
lean_ctor_set(x_32, 15, x_29);
lean_ctor_set(x_32, 16, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*17, x_21);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_14);
x_15 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 10);
x_7 = l_Lean_PersistentArray_push___redArg(x_6, x_1);
lean_ctor_set(x_4, 10, x_7);
x_8 = lean_st_ref_set(x_2, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*17);
x_20 = lean_ctor_get(x_4, 8);
x_21 = lean_ctor_get(x_4, 9);
x_22 = lean_ctor_get(x_4, 10);
x_23 = lean_ctor_get(x_4, 11);
x_24 = lean_ctor_get(x_4, 12);
x_25 = lean_ctor_get(x_4, 13);
x_26 = lean_ctor_get(x_4, 14);
x_27 = lean_ctor_get(x_4, 15);
x_28 = lean_ctor_get(x_4, 16);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_29 = l_Lean_PersistentArray_push___redArg(x_22, x_1);
x_30 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_13);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_15);
lean_ctor_set(x_30, 5, x_16);
lean_ctor_set(x_30, 6, x_17);
lean_ctor_set(x_30, 7, x_18);
lean_ctor_set(x_30, 8, x_20);
lean_ctor_set(x_30, 9, x_21);
lean_ctor_set(x_30, 10, x_29);
lean_ctor_set(x_30, 11, x_23);
lean_ctor_set(x_30, 12, x_24);
lean_ctor_set(x_30, 13, x_25);
lean_ctor_set(x_30, 14, x_26);
lean_ctor_set(x_30, 15, x_27);
lean_ctor_set(x_30, 16, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*17, x_19);
x_31 = lean_st_ref_set(x_2, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_mkEq(x_1, x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_15);
x_16 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_15, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_16);
lean_inc(x_4);
lean_inc_ref(x_1);
x_19 = lean_grind_internalize(x_1, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_20 = lean_grind_internalize(x_2, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_22);
lean_inc(x_4);
lean_inc_ref(x_1);
x_23 = lean_grind_internalize(x_1, x_4, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_24 = lean_grind_internalize(x_2, x_4, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_23;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_addNewEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_15 = lean_grind_internalize(x_3, x_2, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_dec_ref(x_15);
if (x_4 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_getTrueExpr___redArg(x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_18 = l_Lean_Meta_mkEqTrue(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_29 = l_Lean_Meta_mkEqFalse(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_28, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_6 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_17);
lean_inc(x_2);
lean_inc_ref(x_4);
x_18 = lean_grind_internalize(x_4, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_5);
x_19 = lean_grind_internalize(x_5, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_3);
x_22 = lean_grind_internalize(x_3, x_2, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l_Lean_Meta_Grind_getFalseExpr___redArg(x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_25 = l_Lean_Meta_mkEqFalse(x_1, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_24, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc_ref(x_3);
x_14 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_3, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Expr_cleanupAnnotations(x_15);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_16);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_inc_ref(x_19);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_16);
x_26 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_28 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec_ref(x_19);
x_30 = l_Lean_Expr_isApp(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_31 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_33 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1;
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_35 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_26, x_25, x_4, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_27);
x_37 = l_Lean_Expr_isProp(x_26);
lean_dec_ref(x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_19);
x_39 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_38, x_25, x_4, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec_ref(x_25);
lean_dec_ref(x_19);
x_40 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_40;
}
}
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2;
x_2 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_inc_ref(x_1);
x_42 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_4);
lean_dec_ref(x_42);
x_43 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3;
x_44 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__4___redArg(x_43, x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_47);
lean_inc_ref(x_1);
x_48 = l_Lean_MessageData_ofExpr(x_1);
x_49 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg(x_43, x_48, x_8, x_9, x_10, x_11);
lean_dec_ref(x_49);
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = lean_box(0);
goto block_41;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_47;
}
}
block_24:
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_1, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_23;
}
block_41:
{
lean_object* x_34; uint8_t x_35; 
lean_inc_ref(x_1);
x_34 = l_Lean_Expr_cleanupAnnotations(x_1);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec_ref(x_34);
x_13 = x_25;
x_14 = x_26;
x_15 = x_27;
x_16 = x_28;
x_17 = x_29;
x_18 = x_30;
x_19 = x_31;
x_20 = x_32;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_34);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_37 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1;
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_dec_ref(x_34);
x_13 = x_25;
x_14 = x_26;
x_15 = x_27;
x_16 = x_28;
x_17 = x_29;
x_18 = x_30;
x_19 = x_31;
x_20 = x_32;
x_21 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_34);
x_40 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_39, x_38, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_isInconsistent___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0;
x_16 = l_Lean_Core_checkSystem(x_15, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec_ref(x_16);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_25);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec_ref(x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_23, x_24, x_25, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_27);
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_22, 2);
lean_inc(x_34);
lean_dec_ref(x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_32, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_dec_ref(x_35);
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_1);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec_ref(x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_47);
x_48 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec_ref(x_44);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_45, x_46, x_47, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_49);
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_44, 2);
lean_inc(x_56);
lean_dec_ref(x_44);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_54, x_55, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_57);
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_16);
if (x_62 == 0)
{
return x_16;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_16, 0);
lean_inc(x_63);
lean_dec(x_16);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_65 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_3);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
x_68 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_1);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_70 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_1);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_12, 0);
lean_inc(x_74);
lean_dec(x_12);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0;
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_grind_process_new_facts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Expr_isTrue(x_1);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_4);
lean_dec_ref(x_18);
x_19 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_4);
lean_dec_ref(x_23);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_add(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_7);
lean_inc(x_1);
x_12 = l_Lean_FVarId_getType___redArg(x_1, x_7, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_mkFVar(x_1);
x_15 = l_Lean_Meta_Grind_add(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_addHypothesis(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
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
l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__5___redArg___closed__2);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__0);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__1);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__2);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__3);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__4);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__7_spec__7___redArg___closed__5);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__0);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__3);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0_spec__0___closed__1);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__0);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__1);
l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2_spec__2___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__5_spec__5___closed__3);
l_Lean_Meta_Grind_propagateBeta___closed__0 = _init_l_Lean_Meta_Grind_propagateBeta___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__0);
l_Lean_Meta_Grind_propagateBeta___closed__1 = _init_l_Lean_Meta_Grind_propagateBeta___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__1);
l_Lean_Meta_Grind_propagateBeta___closed__2 = _init_l_Lean_Meta_Grind_propagateBeta___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__2);
l_Lean_Meta_Grind_propagateBeta___closed__3 = _init_l_Lean_Meta_Grind_propagateBeta___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__3);
l_Lean_Meta_Grind_propagateBeta___closed__4 = _init_l_Lean_Meta_Grind_propagateBeta___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__4);
l_Lean_Meta_Grind_propagateBeta___closed__5 = _init_l_Lean_Meta_Grind_propagateBeta___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__5);
l_Lean_Meta_Grind_propagateBeta___closed__6 = _init_l_Lean_Meta_Grind_propagateBeta___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__6);
l_Lean_Meta_Grind_propagateBeta___closed__7 = _init_l_Lean_Meta_Grind_propagateBeta___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateBeta___closed__7);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__3_spec__3___redArg___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__8_spec__8___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3);
l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
