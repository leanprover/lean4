// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
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
lean_object* l_Std_Internal_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3;
lean_object* l_Int_gcd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_leadCoeff(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__3(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkDiseqCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Std_Internal_Rat_0__Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_37_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4___boxed(lean_object**);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_toExprProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2;
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2;
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1;
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2;
lean_object* l_Std_Internal_Rat_neg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1;
lean_object* l_Lean_quoteIfNotAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6;
lean_object* l_Std_Internal_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2;
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr;
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
uint8_t l_Std_Internal_Rat_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2;
lean_object* l_Std_Internal_Rat_ceil(lean_object*);
uint8_t l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_collectDecVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isApprox(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_cdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_tail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5;
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCnstrId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___boxed(lean_object**);
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3;
lean_object* l_Std_Internal_Rat_inv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__1(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2;
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkCase(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7;
lean_object* l_Int_Linear_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7;
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Std_Internal_Rat_floor(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Int_Linear_Poly_tail(x_17);
x_20 = l_Int_Linear_Poly_tail(x_18);
x_21 = l_Int_Linear_Poly_leadCoeff(x_17);
lean_dec(x_17);
x_22 = l_Int_Linear_Poly_leadCoeff(x_18);
lean_dec(x_18);
lean_inc(x_19);
x_23 = l_Int_Linear_Poly_mul(x_19, x_22);
x_24 = lean_int_neg(x_21);
lean_inc(x_20);
x_25 = l_Int_Linear_Poly_mul(x_20, x_24);
x_26 = lean_unsigned_to_nat(100000000u);
x_27 = l_Int_Linear_Poly_combine_x27(x_26, x_23, x_25);
lean_inc(x_1);
x_28 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_28, 0, x_1);
if (x_12 == 0)
{
uint8_t x_159; 
x_159 = 0;
x_29 = x_159;
goto block_158;
}
else
{
uint8_t x_160; 
x_160 = 1;
x_29 = x_160;
goto block_158;
}
block_158:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_19);
x_30 = lean_nat_to_int(x_16);
x_31 = lean_int_mul(x_24, x_30);
lean_dec(x_24);
x_32 = l_Int_Linear_Poly_addConst(x_27, x_31);
lean_dec(x_31);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_32, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_1);
x_38 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_38, 0, x_1);
lean_inc(x_20);
x_39 = l_Int_Linear_Poly_addConst(x_20, x_30);
lean_inc(x_22);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_22, x_39, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_44; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = !lean_is_exclusive(x_15);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_15, 0);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Int_Linear_Poly_tail(x_53);
x_56 = l_Int_Linear_Poly_leadCoeff(x_53);
lean_dec(x_53);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1;
x_58 = lean_int_neg(x_56);
lean_dec(x_56);
x_59 = l_Int_Linear_Poly_mul(x_20, x_58);
x_60 = l_Int_Linear_Poly_mul(x_55, x_22);
x_61 = l_Int_Linear_Poly_combine_x27(x_26, x_59, x_60);
x_62 = lean_int_mul(x_58, x_30);
lean_dec(x_30);
lean_dec(x_58);
x_63 = l_Int_Linear_Poly_addConst(x_61, x_62);
lean_dec(x_62);
x_64 = lean_int_mul(x_22, x_54);
lean_dec(x_54);
lean_dec(x_22);
lean_ctor_set_tag(x_15, 9);
lean_ctor_set(x_15, 0, x_1);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_64, x_63, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_apply_10(x_57, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_15, 0);
lean_inc(x_69);
lean_dec(x_15);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Int_Linear_Poly_tail(x_70);
x_73 = l_Int_Linear_Poly_leadCoeff(x_70);
lean_dec(x_70);
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1;
x_75 = lean_int_neg(x_73);
lean_dec(x_73);
x_76 = l_Int_Linear_Poly_mul(x_20, x_75);
x_77 = l_Int_Linear_Poly_mul(x_72, x_22);
x_78 = l_Int_Linear_Poly_combine_x27(x_26, x_76, x_77);
x_79 = lean_int_mul(x_75, x_30);
lean_dec(x_30);
lean_dec(x_75);
x_80 = l_Int_Linear_Poly_addConst(x_78, x_79);
lean_dec(x_79);
x_81 = lean_int_mul(x_22, x_71);
lean_dec(x_71);
lean_dec(x_22);
x_82 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_82, 0, x_1);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_81, x_80, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_apply_10(x_74, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_43);
if (x_87 == 0)
{
return x_43;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_43, 0);
x_89 = lean_ctor_get(x_43, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_36);
if (x_91 == 0)
{
return x_36;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_36, 0);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_36);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_20);
x_95 = lean_nat_to_int(x_16);
x_96 = lean_int_mul(x_22, x_95);
lean_dec(x_22);
x_97 = l_Int_Linear_Poly_addConst(x_27, x_96);
lean_dec(x_96);
x_98 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_97, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_1);
x_103 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_103, 0, x_1);
lean_inc(x_19);
x_104 = l_Int_Linear_Poly_addConst(x_19, x_95);
lean_inc(x_21);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_21, x_104, x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_108 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_106, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_108) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_109; 
lean_dec(x_95);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
x_111 = lean_box(0);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
lean_dec(x_108);
x_116 = !lean_is_exclusive(x_15);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_117 = lean_ctor_get(x_15, 0);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Int_Linear_Poly_tail(x_118);
x_121 = l_Int_Linear_Poly_leadCoeff(x_118);
lean_dec(x_118);
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1;
x_123 = l_Int_Linear_Poly_mul(x_19, x_121);
x_124 = l_Int_Linear_Poly_mul(x_120, x_24);
lean_dec(x_24);
x_125 = l_Int_Linear_Poly_combine_x27(x_26, x_123, x_124);
x_126 = lean_int_mul(x_121, x_95);
lean_dec(x_95);
lean_dec(x_121);
x_127 = l_Int_Linear_Poly_addConst(x_125, x_126);
lean_dec(x_126);
x_128 = lean_int_mul(x_21, x_119);
lean_dec(x_119);
lean_dec(x_21);
lean_ctor_set_tag(x_15, 9);
lean_ctor_set(x_15, 0, x_1);
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_128, x_127, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_apply_10(x_122, x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_133 = lean_ctor_get(x_15, 0);
lean_inc(x_133);
lean_dec(x_15);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Int_Linear_Poly_tail(x_134);
x_137 = l_Int_Linear_Poly_leadCoeff(x_134);
lean_dec(x_134);
x_138 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1;
x_139 = l_Int_Linear_Poly_mul(x_19, x_137);
x_140 = l_Int_Linear_Poly_mul(x_136, x_24);
lean_dec(x_24);
x_141 = l_Int_Linear_Poly_combine_x27(x_26, x_139, x_140);
x_142 = lean_int_mul(x_137, x_95);
lean_dec(x_95);
lean_dec(x_137);
x_143 = l_Int_Linear_Poly_addConst(x_141, x_142);
lean_dec(x_142);
x_144 = lean_int_mul(x_21, x_135);
lean_dec(x_135);
lean_dec(x_21);
x_145 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_145, 0, x_1);
x_146 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_144, x_143, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_apply_10(x_138, x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_95);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_108);
if (x_150 == 0)
{
return x_108;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_108, 0);
x_152 = lean_ctor_get(x_108, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_108);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_95);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_101);
if (x_154 == 0)
{
return x_101;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_101, 0);
x_156 = lean_ctor_get(x_101, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_101);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, assigning variable out of order", 55, 55);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 10);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_nat_dec_eq(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_11);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2;
x_19 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_21, 10);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_nat_dec_eq(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2;
x_27 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_quoteIfNotAtom(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_28);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_37 = lean_int_dec_lt(x_34, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_nat_abs(x_34);
lean_dec(x_34);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_38);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_35);
lean_dec(x_35);
x_45 = lean_string_append(x_44, x_40);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_30);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_28);
x_50 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_nat_abs(x_34);
lean_dec(x_34);
x_52 = lean_nat_sub(x_51, x_32);
lean_dec(x_51);
x_53 = lean_nat_add(x_52, x_32);
lean_dec(x_52);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_53);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_string_append(x_60, x_35);
lean_dec(x_35);
x_62 = lean_string_append(x_61, x_57);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_MessageData_ofFormat(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_30);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_28);
x_67 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_31);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_dec(x_2);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_70 = lean_int_dec_lt(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_nat_abs(x_68);
lean_dec(x_68);
x_72 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_MessageData_ofFormat(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_30);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_28);
x_77 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_nat_abs(x_68);
lean_dec(x_68);
x_79 = lean_nat_sub(x_78, x_32);
lean_dec(x_78);
x_80 = lean_nat_add(x_79, x_32);
lean_dec(x_79);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_MessageData_ofFormat(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_30);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_28);
x_88 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_ctor_get(x_23, 0);
x_90 = lean_ctor_get(x_23, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_23);
x_91 = l_Lean_quoteIfNotAtom(x_89);
x_92 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
lean_dec(x_2);
x_100 = l___private_Init_Data_Repr_0__Nat_reprFast(x_96);
x_101 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_102 = lean_int_dec_lt(x_99, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_nat_abs(x_99);
lean_dec(x_99);
x_104 = l___private_Init_Data_Repr_0__Nat_reprFast(x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_string_append(x_108, x_100);
lean_dec(x_100);
x_110 = lean_string_append(x_109, x_105);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_MessageData_ofFormat(x_111);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_95);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_92);
x_115 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_116 = lean_nat_abs(x_99);
lean_dec(x_99);
x_117 = lean_nat_sub(x_116, x_97);
lean_dec(x_116);
x_118 = lean_nat_add(x_117, x_97);
lean_dec(x_117);
x_119 = l___private_Init_Data_Repr_0__Nat_reprFast(x_118);
x_120 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_100);
lean_dec(x_100);
x_127 = lean_string_append(x_126, x_122);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_MessageData_ofFormat(x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_95);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_92);
x_132 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_131, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_96);
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
lean_dec(x_2);
x_134 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_135 = lean_int_dec_lt(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = lean_nat_abs(x_133);
lean_dec(x_133);
x_137 = l___private_Init_Data_Repr_0__Nat_reprFast(x_136);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_95);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_92);
x_142 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_143 = lean_nat_abs(x_133);
lean_dec(x_133);
x_144 = lean_nat_sub(x_143, x_97);
lean_dec(x_143);
x_145 = lean_nat_add(x_144, x_97);
lean_dec(x_144);
x_146 = l___private_Init_Data_Repr_0__Nat_reprFast(x_145);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Lean_MessageData_ofFormat(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_95);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_92);
x_153 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
return x_153;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 13);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_17, 13);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_19, 10);
x_27 = l_Lean_PersistentArray_push___rarg(x_26, x_2);
lean_ctor_set(x_19, 10, x_27);
x_28 = lean_st_ref_set(x_3, x_17, x_20);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_ctor_get(x_19, 2);
x_38 = lean_ctor_get(x_19, 3);
x_39 = lean_ctor_get(x_19, 4);
x_40 = lean_ctor_get(x_19, 5);
x_41 = lean_ctor_get(x_19, 6);
x_42 = lean_ctor_get(x_19, 7);
x_43 = lean_ctor_get(x_19, 8);
x_44 = lean_ctor_get(x_19, 9);
x_45 = lean_ctor_get(x_19, 10);
x_46 = lean_ctor_get(x_19, 11);
x_47 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_48 = lean_ctor_get(x_19, 12);
x_49 = lean_ctor_get(x_19, 13);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_50 = l_Lean_PersistentArray_push___rarg(x_45, x_2);
x_51 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_38);
lean_ctor_set(x_51, 4, x_39);
lean_ctor_set(x_51, 5, x_40);
lean_ctor_set(x_51, 6, x_41);
lean_ctor_set(x_51, 7, x_42);
lean_ctor_set(x_51, 8, x_43);
lean_ctor_set(x_51, 9, x_44);
lean_ctor_set(x_51, 10, x_50);
lean_ctor_set(x_51, 11, x_46);
lean_ctor_set(x_51, 12, x_48);
lean_ctor_set(x_51, 13, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*14, x_47);
lean_ctor_set(x_18, 1, x_51);
x_52 = lean_st_ref_set(x_3, x_17, x_20);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_57 = lean_ctor_get(x_18, 0);
lean_inc(x_57);
lean_dec(x_18);
x_58 = lean_ctor_get(x_19, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_19, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 10);
lean_inc(x_68);
x_69 = lean_ctor_get(x_19, 11);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_71 = lean_ctor_get(x_19, 12);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 13);
lean_inc(x_72);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_73 = x_19;
} else {
 lean_dec_ref(x_19);
 x_73 = lean_box(0);
}
x_74 = l_Lean_PersistentArray_push___rarg(x_68, x_2);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 14, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_58);
lean_ctor_set(x_75, 1, x_59);
lean_ctor_set(x_75, 2, x_60);
lean_ctor_set(x_75, 3, x_61);
lean_ctor_set(x_75, 4, x_62);
lean_ctor_set(x_75, 5, x_63);
lean_ctor_set(x_75, 6, x_64);
lean_ctor_set(x_75, 7, x_65);
lean_ctor_set(x_75, 8, x_66);
lean_ctor_set(x_75, 9, x_67);
lean_ctor_set(x_75, 10, x_74);
lean_ctor_set(x_75, 11, x_69);
lean_ctor_set(x_75, 12, x_71);
lean_ctor_set(x_75, 13, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*14, x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_17, 13, x_76);
x_77 = lean_st_ref_set(x_3, x_17, x_20);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_82 = lean_ctor_get(x_17, 0);
x_83 = lean_ctor_get(x_17, 1);
x_84 = lean_ctor_get(x_17, 2);
x_85 = lean_ctor_get(x_17, 3);
x_86 = lean_ctor_get(x_17, 4);
x_87 = lean_ctor_get(x_17, 5);
x_88 = lean_ctor_get(x_17, 6);
x_89 = lean_ctor_get_uint8(x_17, sizeof(void*)*15);
x_90 = lean_ctor_get(x_17, 7);
x_91 = lean_ctor_get(x_17, 8);
x_92 = lean_ctor_get(x_17, 9);
x_93 = lean_ctor_get(x_17, 10);
x_94 = lean_ctor_get(x_17, 11);
x_95 = lean_ctor_get(x_17, 12);
x_96 = lean_ctor_get(x_17, 14);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_17);
x_97 = lean_ctor_get(x_18, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_98 = x_18;
} else {
 lean_dec_ref(x_18);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_19, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_19, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_19, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_19, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_19, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_19, 6);
lean_inc(x_105);
x_106 = lean_ctor_get(x_19, 7);
lean_inc(x_106);
x_107 = lean_ctor_get(x_19, 8);
lean_inc(x_107);
x_108 = lean_ctor_get(x_19, 9);
lean_inc(x_108);
x_109 = lean_ctor_get(x_19, 10);
lean_inc(x_109);
x_110 = lean_ctor_get(x_19, 11);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_112 = lean_ctor_get(x_19, 12);
lean_inc(x_112);
x_113 = lean_ctor_get(x_19, 13);
lean_inc(x_113);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_114 = x_19;
} else {
 lean_dec_ref(x_19);
 x_114 = lean_box(0);
}
x_115 = l_Lean_PersistentArray_push___rarg(x_109, x_2);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 14, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_100);
lean_ctor_set(x_116, 2, x_101);
lean_ctor_set(x_116, 3, x_102);
lean_ctor_set(x_116, 4, x_103);
lean_ctor_set(x_116, 5, x_104);
lean_ctor_set(x_116, 6, x_105);
lean_ctor_set(x_116, 7, x_106);
lean_ctor_set(x_116, 8, x_107);
lean_ctor_set(x_116, 9, x_108);
lean_ctor_set(x_116, 10, x_115);
lean_ctor_set(x_116, 11, x_110);
lean_ctor_set(x_116, 12, x_112);
lean_ctor_set(x_116, 13, x_113);
lean_ctor_set_uint8(x_116, sizeof(void*)*14, x_111);
if (lean_is_scalar(x_98)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_98;
}
lean_ctor_set(x_117, 0, x_97);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_118, 0, x_82);
lean_ctor_set(x_118, 1, x_83);
lean_ctor_set(x_118, 2, x_84);
lean_ctor_set(x_118, 3, x_85);
lean_ctor_set(x_118, 4, x_86);
lean_ctor_set(x_118, 5, x_87);
lean_ctor_set(x_118, 6, x_88);
lean_ctor_set(x_118, 7, x_90);
lean_ctor_set(x_118, 8, x_91);
lean_ctor_set(x_118, 9, x_92);
lean_ctor_set(x_118, 10, x_93);
lean_ctor_set(x_118, 11, x_94);
lean_ctor_set(x_118, 12, x_95);
lean_ctor_set(x_118, 13, x_117);
lean_ctor_set(x_118, 14, x_96);
lean_ctor_set_uint8(x_118, sizeof(void*)*15, x_89);
x_119 = lean_st_ref_set(x_3, x_118, x_20);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_12);
if (x_124 == 0)
{
return x_12;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_12, 0);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_12);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 13);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 13);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_16, 10);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_25 = l_Lean_PersistentArray_push___rarg(x_23, x_24);
lean_ctor_set(x_16, 10, x_25);
x_26 = lean_st_ref_set(x_2, x_14, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
x_35 = lean_ctor_get(x_16, 2);
x_36 = lean_ctor_get(x_16, 3);
x_37 = lean_ctor_get(x_16, 4);
x_38 = lean_ctor_get(x_16, 5);
x_39 = lean_ctor_get(x_16, 6);
x_40 = lean_ctor_get(x_16, 7);
x_41 = lean_ctor_get(x_16, 8);
x_42 = lean_ctor_get(x_16, 9);
x_43 = lean_ctor_get(x_16, 10);
x_44 = lean_ctor_get(x_16, 11);
x_45 = lean_ctor_get_uint8(x_16, sizeof(void*)*14);
x_46 = lean_ctor_get(x_16, 12);
x_47 = lean_ctor_get(x_16, 13);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_49 = l_Lean_PersistentArray_push___rarg(x_43, x_48);
x_50 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_34);
lean_ctor_set(x_50, 2, x_35);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_37);
lean_ctor_set(x_50, 5, x_38);
lean_ctor_set(x_50, 6, x_39);
lean_ctor_set(x_50, 7, x_40);
lean_ctor_set(x_50, 8, x_41);
lean_ctor_set(x_50, 9, x_42);
lean_ctor_set(x_50, 10, x_49);
lean_ctor_set(x_50, 11, x_44);
lean_ctor_set(x_50, 12, x_46);
lean_ctor_set(x_50, 13, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*14, x_45);
lean_ctor_set(x_15, 1, x_50);
x_51 = lean_st_ref_set(x_2, x_14, x_17);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
lean_dec(x_15);
x_57 = lean_ctor_get(x_16, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_16, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_16, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_16, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_16, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_16, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_16, 8);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 9);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 10);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 11);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_16, sizeof(void*)*14);
x_70 = lean_ctor_get(x_16, 12);
lean_inc(x_70);
x_71 = lean_ctor_get(x_16, 13);
lean_inc(x_71);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 lean_ctor_release(x_16, 8);
 lean_ctor_release(x_16, 9);
 lean_ctor_release(x_16, 10);
 lean_ctor_release(x_16, 11);
 lean_ctor_release(x_16, 12);
 lean_ctor_release(x_16, 13);
 x_72 = x_16;
} else {
 lean_dec_ref(x_16);
 x_72 = lean_box(0);
}
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_74 = l_Lean_PersistentArray_push___rarg(x_67, x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 14, 1);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_58);
lean_ctor_set(x_75, 2, x_59);
lean_ctor_set(x_75, 3, x_60);
lean_ctor_set(x_75, 4, x_61);
lean_ctor_set(x_75, 5, x_62);
lean_ctor_set(x_75, 6, x_63);
lean_ctor_set(x_75, 7, x_64);
lean_ctor_set(x_75, 8, x_65);
lean_ctor_set(x_75, 9, x_66);
lean_ctor_set(x_75, 10, x_74);
lean_ctor_set(x_75, 11, x_68);
lean_ctor_set(x_75, 12, x_70);
lean_ctor_set(x_75, 13, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*14, x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_56);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_14, 13, x_76);
x_77 = lean_st_ref_set(x_2, x_14, x_17);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_82 = lean_ctor_get(x_14, 0);
x_83 = lean_ctor_get(x_14, 1);
x_84 = lean_ctor_get(x_14, 2);
x_85 = lean_ctor_get(x_14, 3);
x_86 = lean_ctor_get(x_14, 4);
x_87 = lean_ctor_get(x_14, 5);
x_88 = lean_ctor_get(x_14, 6);
x_89 = lean_ctor_get_uint8(x_14, sizeof(void*)*15);
x_90 = lean_ctor_get(x_14, 7);
x_91 = lean_ctor_get(x_14, 8);
x_92 = lean_ctor_get(x_14, 9);
x_93 = lean_ctor_get(x_14, 10);
x_94 = lean_ctor_get(x_14, 11);
x_95 = lean_ctor_get(x_14, 12);
x_96 = lean_ctor_get(x_14, 14);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_14);
x_97 = lean_ctor_get(x_15, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_98 = x_15;
} else {
 lean_dec_ref(x_15);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_16, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_16, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_16, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_16, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_16, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_16, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_16, 6);
lean_inc(x_105);
x_106 = lean_ctor_get(x_16, 7);
lean_inc(x_106);
x_107 = lean_ctor_get(x_16, 8);
lean_inc(x_107);
x_108 = lean_ctor_get(x_16, 9);
lean_inc(x_108);
x_109 = lean_ctor_get(x_16, 10);
lean_inc(x_109);
x_110 = lean_ctor_get(x_16, 11);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_16, sizeof(void*)*14);
x_112 = lean_ctor_get(x_16, 12);
lean_inc(x_112);
x_113 = lean_ctor_get(x_16, 13);
lean_inc(x_113);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 lean_ctor_release(x_16, 8);
 lean_ctor_release(x_16, 9);
 lean_ctor_release(x_16, 10);
 lean_ctor_release(x_16, 11);
 lean_ctor_release(x_16, 12);
 lean_ctor_release(x_16, 13);
 x_114 = x_16;
} else {
 lean_dec_ref(x_16);
 x_114 = lean_box(0);
}
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_116 = l_Lean_PersistentArray_push___rarg(x_109, x_115);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 14, 1);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_99);
lean_ctor_set(x_117, 1, x_100);
lean_ctor_set(x_117, 2, x_101);
lean_ctor_set(x_117, 3, x_102);
lean_ctor_set(x_117, 4, x_103);
lean_ctor_set(x_117, 5, x_104);
lean_ctor_set(x_117, 6, x_105);
lean_ctor_set(x_117, 7, x_106);
lean_ctor_set(x_117, 8, x_107);
lean_ctor_set(x_117, 9, x_108);
lean_ctor_set(x_117, 10, x_116);
lean_ctor_set(x_117, 11, x_110);
lean_ctor_set(x_117, 12, x_112);
lean_ctor_set(x_117, 13, x_113);
lean_ctor_set_uint8(x_117, sizeof(void*)*14, x_111);
if (lean_is_scalar(x_98)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_98;
}
lean_ctor_set(x_118, 0, x_97);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_119, 0, x_82);
lean_ctor_set(x_119, 1, x_83);
lean_ctor_set(x_119, 2, x_84);
lean_ctor_set(x_119, 3, x_85);
lean_ctor_set(x_119, 4, x_86);
lean_ctor_set(x_119, 5, x_87);
lean_ctor_set(x_119, 6, x_88);
lean_ctor_set(x_119, 7, x_90);
lean_ctor_set(x_119, 8, x_91);
lean_ctor_set(x_119, 9, x_92);
lean_ctor_set(x_119, 10, x_93);
lean_ctor_set(x_119, 11, x_94);
lean_ctor_set(x_119, 12, x_95);
lean_ctor_set(x_119, 13, x_118);
lean_ctor_set(x_119, 14, x_96);
lean_ctor_set_uint8(x_119, sizeof(void*)*15, x_89);
x_120 = lean_st_ref_set(x_2, x_119, x_17);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_11);
if (x_125 == 0)
{
return x_11;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_11, 0);
x_127 = lean_ctor_get(x_11, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_11);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 13);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_17, 13);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 10);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_28 = l_Lean_PersistentArray_set___rarg(x_26, x_1, x_27);
lean_ctor_set(x_19, 10, x_28);
x_29 = lean_st_ref_set(x_7, x_17, x_20);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Int_Linear_Poly_eval_x3f(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_31, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l_Std_Internal_Rat_neg(x_38);
x_40 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_31, 1, x_40);
lean_ctor_set(x_31, 0, x_4);
x_41 = l_Std_Internal_Rat_inv(x_31);
x_42 = l_Std_Internal_Rat_mul(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
lean_inc(x_42);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_7, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 13);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 13);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_47, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_48, 10);
x_56 = l_Lean_PersistentArray_set___rarg(x_55, x_1, x_42);
lean_ctor_set(x_48, 10, x_56);
x_57 = lean_st_ref_set(x_7, x_46, x_49);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
x_62 = lean_ctor_get(x_48, 2);
x_63 = lean_ctor_get(x_48, 3);
x_64 = lean_ctor_get(x_48, 4);
x_65 = lean_ctor_get(x_48, 5);
x_66 = lean_ctor_get(x_48, 6);
x_67 = lean_ctor_get(x_48, 7);
x_68 = lean_ctor_get(x_48, 8);
x_69 = lean_ctor_get(x_48, 9);
x_70 = lean_ctor_get(x_48, 10);
x_71 = lean_ctor_get(x_48, 11);
x_72 = lean_ctor_get_uint8(x_48, sizeof(void*)*14);
x_73 = lean_ctor_get(x_48, 12);
x_74 = lean_ctor_get(x_48, 13);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_75 = l_Lean_PersistentArray_set___rarg(x_70, x_1, x_42);
x_76 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_61);
lean_ctor_set(x_76, 2, x_62);
lean_ctor_set(x_76, 3, x_63);
lean_ctor_set(x_76, 4, x_64);
lean_ctor_set(x_76, 5, x_65);
lean_ctor_set(x_76, 6, x_66);
lean_ctor_set(x_76, 7, x_67);
lean_ctor_set(x_76, 8, x_68);
lean_ctor_set(x_76, 9, x_69);
lean_ctor_set(x_76, 10, x_75);
lean_ctor_set(x_76, 11, x_71);
lean_ctor_set(x_76, 12, x_73);
lean_ctor_set(x_76, 13, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*14, x_72);
lean_ctor_set(x_47, 1, x_76);
x_77 = lean_st_ref_set(x_7, x_46, x_49);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
lean_dec(x_47);
x_81 = lean_ctor_get(x_48, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_48, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_48, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_48, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_48, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_48, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_48, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_48, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_48, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_48, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_48, 11);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_48, sizeof(void*)*14);
x_94 = lean_ctor_get(x_48, 12);
lean_inc(x_94);
x_95 = lean_ctor_get(x_48, 13);
lean_inc(x_95);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 lean_ctor_release(x_48, 6);
 lean_ctor_release(x_48, 7);
 lean_ctor_release(x_48, 8);
 lean_ctor_release(x_48, 9);
 lean_ctor_release(x_48, 10);
 lean_ctor_release(x_48, 11);
 lean_ctor_release(x_48, 12);
 lean_ctor_release(x_48, 13);
 x_96 = x_48;
} else {
 lean_dec_ref(x_48);
 x_96 = lean_box(0);
}
x_97 = l_Lean_PersistentArray_set___rarg(x_91, x_1, x_42);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 14, 1);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_82);
lean_ctor_set(x_98, 2, x_83);
lean_ctor_set(x_98, 3, x_84);
lean_ctor_set(x_98, 4, x_85);
lean_ctor_set(x_98, 5, x_86);
lean_ctor_set(x_98, 6, x_87);
lean_ctor_set(x_98, 7, x_88);
lean_ctor_set(x_98, 8, x_89);
lean_ctor_set(x_98, 9, x_90);
lean_ctor_set(x_98, 10, x_97);
lean_ctor_set(x_98, 11, x_92);
lean_ctor_set(x_98, 12, x_94);
lean_ctor_set(x_98, 13, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*14, x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_80);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_46, 13, x_99);
x_100 = lean_st_ref_set(x_7, x_46, x_49);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_101);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = lean_ctor_get(x_46, 4);
x_108 = lean_ctor_get(x_46, 5);
x_109 = lean_ctor_get(x_46, 6);
x_110 = lean_ctor_get_uint8(x_46, sizeof(void*)*15);
x_111 = lean_ctor_get(x_46, 7);
x_112 = lean_ctor_get(x_46, 8);
x_113 = lean_ctor_get(x_46, 9);
x_114 = lean_ctor_get(x_46, 10);
x_115 = lean_ctor_get(x_46, 11);
x_116 = lean_ctor_get(x_46, 12);
x_117 = lean_ctor_get(x_46, 14);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_46);
x_118 = lean_ctor_get(x_47, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_119 = x_47;
} else {
 lean_dec_ref(x_47);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_48, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_48, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_48, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_48, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_48, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_48, 5);
lean_inc(x_125);
x_126 = lean_ctor_get(x_48, 6);
lean_inc(x_126);
x_127 = lean_ctor_get(x_48, 7);
lean_inc(x_127);
x_128 = lean_ctor_get(x_48, 8);
lean_inc(x_128);
x_129 = lean_ctor_get(x_48, 9);
lean_inc(x_129);
x_130 = lean_ctor_get(x_48, 10);
lean_inc(x_130);
x_131 = lean_ctor_get(x_48, 11);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_48, sizeof(void*)*14);
x_133 = lean_ctor_get(x_48, 12);
lean_inc(x_133);
x_134 = lean_ctor_get(x_48, 13);
lean_inc(x_134);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 lean_ctor_release(x_48, 6);
 lean_ctor_release(x_48, 7);
 lean_ctor_release(x_48, 8);
 lean_ctor_release(x_48, 9);
 lean_ctor_release(x_48, 10);
 lean_ctor_release(x_48, 11);
 lean_ctor_release(x_48, 12);
 lean_ctor_release(x_48, 13);
 x_135 = x_48;
} else {
 lean_dec_ref(x_48);
 x_135 = lean_box(0);
}
x_136 = l_Lean_PersistentArray_set___rarg(x_130, x_1, x_42);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 14, 1);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_120);
lean_ctor_set(x_137, 1, x_121);
lean_ctor_set(x_137, 2, x_122);
lean_ctor_set(x_137, 3, x_123);
lean_ctor_set(x_137, 4, x_124);
lean_ctor_set(x_137, 5, x_125);
lean_ctor_set(x_137, 6, x_126);
lean_ctor_set(x_137, 7, x_127);
lean_ctor_set(x_137, 8, x_128);
lean_ctor_set(x_137, 9, x_129);
lean_ctor_set(x_137, 10, x_136);
lean_ctor_set(x_137, 11, x_131);
lean_ctor_set(x_137, 12, x_133);
lean_ctor_set(x_137, 13, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*14, x_132);
if (lean_is_scalar(x_119)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_119;
}
lean_ctor_set(x_138, 0, x_118);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_139, 0, x_103);
lean_ctor_set(x_139, 1, x_104);
lean_ctor_set(x_139, 2, x_105);
lean_ctor_set(x_139, 3, x_106);
lean_ctor_set(x_139, 4, x_107);
lean_ctor_set(x_139, 5, x_108);
lean_ctor_set(x_139, 6, x_109);
lean_ctor_set(x_139, 7, x_111);
lean_ctor_set(x_139, 8, x_112);
lean_ctor_set(x_139, 9, x_113);
lean_ctor_set(x_139, 10, x_114);
lean_ctor_set(x_139, 11, x_115);
lean_ctor_set(x_139, 12, x_116);
lean_ctor_set(x_139, 13, x_138);
lean_ctor_set(x_139, 14, x_117);
lean_ctor_set_uint8(x_139, sizeof(void*)*15, x_110);
x_140 = lean_st_ref_set(x_7, x_139, x_49);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_143 = lean_ctor_get(x_31, 1);
lean_inc(x_143);
lean_dec(x_31);
x_144 = lean_ctor_get(x_32, 0);
lean_inc(x_144);
lean_dec(x_32);
x_145 = l_Std_Internal_Rat_neg(x_144);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Std_Internal_Rat_inv(x_147);
x_149 = l_Std_Internal_Rat_mul(x_145, x_148);
lean_dec(x_148);
lean_dec(x_145);
lean_inc(x_149);
x_150 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_149, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_143);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_st_ref_take(x_7, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_153, 13);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_153, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_153, 4);
lean_inc(x_161);
x_162 = lean_ctor_get(x_153, 5);
lean_inc(x_162);
x_163 = lean_ctor_get(x_153, 6);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_153, sizeof(void*)*15);
x_165 = lean_ctor_get(x_153, 7);
lean_inc(x_165);
x_166 = lean_ctor_get(x_153, 8);
lean_inc(x_166);
x_167 = lean_ctor_get(x_153, 9);
lean_inc(x_167);
x_168 = lean_ctor_get(x_153, 10);
lean_inc(x_168);
x_169 = lean_ctor_get(x_153, 11);
lean_inc(x_169);
x_170 = lean_ctor_get(x_153, 12);
lean_inc(x_170);
x_171 = lean_ctor_get(x_153, 14);
lean_inc(x_171);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 lean_ctor_release(x_153, 4);
 lean_ctor_release(x_153, 5);
 lean_ctor_release(x_153, 6);
 lean_ctor_release(x_153, 7);
 lean_ctor_release(x_153, 8);
 lean_ctor_release(x_153, 9);
 lean_ctor_release(x_153, 10);
 lean_ctor_release(x_153, 11);
 lean_ctor_release(x_153, 12);
 lean_ctor_release(x_153, 13);
 lean_ctor_release(x_153, 14);
 x_172 = x_153;
} else {
 lean_dec_ref(x_153);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_154, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_174 = x_154;
} else {
 lean_dec_ref(x_154);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_155, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_155, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_155, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_155, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_155, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_155, 5);
lean_inc(x_180);
x_181 = lean_ctor_get(x_155, 6);
lean_inc(x_181);
x_182 = lean_ctor_get(x_155, 7);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 8);
lean_inc(x_183);
x_184 = lean_ctor_get(x_155, 9);
lean_inc(x_184);
x_185 = lean_ctor_get(x_155, 10);
lean_inc(x_185);
x_186 = lean_ctor_get(x_155, 11);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_155, sizeof(void*)*14);
x_188 = lean_ctor_get(x_155, 12);
lean_inc(x_188);
x_189 = lean_ctor_get(x_155, 13);
lean_inc(x_189);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 lean_ctor_release(x_155, 6);
 lean_ctor_release(x_155, 7);
 lean_ctor_release(x_155, 8);
 lean_ctor_release(x_155, 9);
 lean_ctor_release(x_155, 10);
 lean_ctor_release(x_155, 11);
 lean_ctor_release(x_155, 12);
 lean_ctor_release(x_155, 13);
 x_190 = x_155;
} else {
 lean_dec_ref(x_155);
 x_190 = lean_box(0);
}
x_191 = l_Lean_PersistentArray_set___rarg(x_185, x_1, x_149);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 14, 1);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_175);
lean_ctor_set(x_192, 1, x_176);
lean_ctor_set(x_192, 2, x_177);
lean_ctor_set(x_192, 3, x_178);
lean_ctor_set(x_192, 4, x_179);
lean_ctor_set(x_192, 5, x_180);
lean_ctor_set(x_192, 6, x_181);
lean_ctor_set(x_192, 7, x_182);
lean_ctor_set(x_192, 8, x_183);
lean_ctor_set(x_192, 9, x_184);
lean_ctor_set(x_192, 10, x_191);
lean_ctor_set(x_192, 11, x_186);
lean_ctor_set(x_192, 12, x_188);
lean_ctor_set(x_192, 13, x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*14, x_187);
if (lean_is_scalar(x_174)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_174;
}
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_192);
if (lean_is_scalar(x_172)) {
 x_194 = lean_alloc_ctor(0, 15, 1);
} else {
 x_194 = x_172;
}
lean_ctor_set(x_194, 0, x_157);
lean_ctor_set(x_194, 1, x_158);
lean_ctor_set(x_194, 2, x_159);
lean_ctor_set(x_194, 3, x_160);
lean_ctor_set(x_194, 4, x_161);
lean_ctor_set(x_194, 5, x_162);
lean_ctor_set(x_194, 6, x_163);
lean_ctor_set(x_194, 7, x_165);
lean_ctor_set(x_194, 8, x_166);
lean_ctor_set(x_194, 9, x_167);
lean_ctor_set(x_194, 10, x_168);
lean_ctor_set(x_194, 11, x_169);
lean_ctor_set(x_194, 12, x_170);
lean_ctor_set(x_194, 13, x_193);
lean_ctor_set(x_194, 14, x_171);
lean_ctor_set_uint8(x_194, sizeof(void*)*15, x_164);
x_195 = lean_st_ref_set(x_7, x_194, x_156);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_198 = lean_ctor_get(x_19, 0);
x_199 = lean_ctor_get(x_19, 1);
x_200 = lean_ctor_get(x_19, 2);
x_201 = lean_ctor_get(x_19, 3);
x_202 = lean_ctor_get(x_19, 4);
x_203 = lean_ctor_get(x_19, 5);
x_204 = lean_ctor_get(x_19, 6);
x_205 = lean_ctor_get(x_19, 7);
x_206 = lean_ctor_get(x_19, 8);
x_207 = lean_ctor_get(x_19, 9);
x_208 = lean_ctor_get(x_19, 10);
x_209 = lean_ctor_get(x_19, 11);
x_210 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_211 = lean_ctor_get(x_19, 12);
x_212 = lean_ctor_get(x_19, 13);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_19);
x_213 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_214 = l_Lean_PersistentArray_set___rarg(x_208, x_1, x_213);
x_215 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_215, 0, x_198);
lean_ctor_set(x_215, 1, x_199);
lean_ctor_set(x_215, 2, x_200);
lean_ctor_set(x_215, 3, x_201);
lean_ctor_set(x_215, 4, x_202);
lean_ctor_set(x_215, 5, x_203);
lean_ctor_set(x_215, 6, x_204);
lean_ctor_set(x_215, 7, x_205);
lean_ctor_set(x_215, 8, x_206);
lean_ctor_set(x_215, 9, x_207);
lean_ctor_set(x_215, 10, x_214);
lean_ctor_set(x_215, 11, x_209);
lean_ctor_set(x_215, 12, x_211);
lean_ctor_set(x_215, 13, x_212);
lean_ctor_set_uint8(x_215, sizeof(void*)*14, x_210);
lean_ctor_set(x_18, 1, x_215);
x_216 = lean_st_ref_set(x_7, x_17, x_20);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = l_Int_Linear_Poly_eval_x3f(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_4);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_220);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_3);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_223 = x_218;
} else {
 lean_dec_ref(x_218);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_219, 0);
lean_inc(x_224);
lean_dec(x_219);
x_225 = l_Std_Internal_Rat_neg(x_224);
x_226 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_4);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Std_Internal_Rat_inv(x_227);
x_229 = l_Std_Internal_Rat_mul(x_225, x_228);
lean_dec(x_228);
lean_dec(x_225);
lean_inc(x_229);
x_230 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_229, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_222);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_st_ref_take(x_7, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 13);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_232, 1);
lean_inc(x_236);
lean_dec(x_232);
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_233, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 4);
lean_inc(x_241);
x_242 = lean_ctor_get(x_233, 5);
lean_inc(x_242);
x_243 = lean_ctor_get(x_233, 6);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_233, sizeof(void*)*15);
x_245 = lean_ctor_get(x_233, 7);
lean_inc(x_245);
x_246 = lean_ctor_get(x_233, 8);
lean_inc(x_246);
x_247 = lean_ctor_get(x_233, 9);
lean_inc(x_247);
x_248 = lean_ctor_get(x_233, 10);
lean_inc(x_248);
x_249 = lean_ctor_get(x_233, 11);
lean_inc(x_249);
x_250 = lean_ctor_get(x_233, 12);
lean_inc(x_250);
x_251 = lean_ctor_get(x_233, 14);
lean_inc(x_251);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 lean_ctor_release(x_233, 6);
 lean_ctor_release(x_233, 7);
 lean_ctor_release(x_233, 8);
 lean_ctor_release(x_233, 9);
 lean_ctor_release(x_233, 10);
 lean_ctor_release(x_233, 11);
 lean_ctor_release(x_233, 12);
 lean_ctor_release(x_233, 13);
 lean_ctor_release(x_233, 14);
 x_252 = x_233;
} else {
 lean_dec_ref(x_233);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_234, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_254 = x_234;
} else {
 lean_dec_ref(x_234);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_235, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_235, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_235, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_235, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_235, 4);
lean_inc(x_259);
x_260 = lean_ctor_get(x_235, 5);
lean_inc(x_260);
x_261 = lean_ctor_get(x_235, 6);
lean_inc(x_261);
x_262 = lean_ctor_get(x_235, 7);
lean_inc(x_262);
x_263 = lean_ctor_get(x_235, 8);
lean_inc(x_263);
x_264 = lean_ctor_get(x_235, 9);
lean_inc(x_264);
x_265 = lean_ctor_get(x_235, 10);
lean_inc(x_265);
x_266 = lean_ctor_get(x_235, 11);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_235, sizeof(void*)*14);
x_268 = lean_ctor_get(x_235, 12);
lean_inc(x_268);
x_269 = lean_ctor_get(x_235, 13);
lean_inc(x_269);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 lean_ctor_release(x_235, 5);
 lean_ctor_release(x_235, 6);
 lean_ctor_release(x_235, 7);
 lean_ctor_release(x_235, 8);
 lean_ctor_release(x_235, 9);
 lean_ctor_release(x_235, 10);
 lean_ctor_release(x_235, 11);
 lean_ctor_release(x_235, 12);
 lean_ctor_release(x_235, 13);
 x_270 = x_235;
} else {
 lean_dec_ref(x_235);
 x_270 = lean_box(0);
}
x_271 = l_Lean_PersistentArray_set___rarg(x_265, x_1, x_229);
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(0, 14, 1);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_255);
lean_ctor_set(x_272, 1, x_256);
lean_ctor_set(x_272, 2, x_257);
lean_ctor_set(x_272, 3, x_258);
lean_ctor_set(x_272, 4, x_259);
lean_ctor_set(x_272, 5, x_260);
lean_ctor_set(x_272, 6, x_261);
lean_ctor_set(x_272, 7, x_262);
lean_ctor_set(x_272, 8, x_263);
lean_ctor_set(x_272, 9, x_264);
lean_ctor_set(x_272, 10, x_271);
lean_ctor_set(x_272, 11, x_266);
lean_ctor_set(x_272, 12, x_268);
lean_ctor_set(x_272, 13, x_269);
lean_ctor_set_uint8(x_272, sizeof(void*)*14, x_267);
if (lean_is_scalar(x_254)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_254;
}
lean_ctor_set(x_273, 0, x_253);
lean_ctor_set(x_273, 1, x_272);
if (lean_is_scalar(x_252)) {
 x_274 = lean_alloc_ctor(0, 15, 1);
} else {
 x_274 = x_252;
}
lean_ctor_set(x_274, 0, x_237);
lean_ctor_set(x_274, 1, x_238);
lean_ctor_set(x_274, 2, x_239);
lean_ctor_set(x_274, 3, x_240);
lean_ctor_set(x_274, 4, x_241);
lean_ctor_set(x_274, 5, x_242);
lean_ctor_set(x_274, 6, x_243);
lean_ctor_set(x_274, 7, x_245);
lean_ctor_set(x_274, 8, x_246);
lean_ctor_set(x_274, 9, x_247);
lean_ctor_set(x_274, 10, x_248);
lean_ctor_set(x_274, 11, x_249);
lean_ctor_set(x_274, 12, x_250);
lean_ctor_set(x_274, 13, x_273);
lean_ctor_set(x_274, 14, x_251);
lean_ctor_set_uint8(x_274, sizeof(void*)*15, x_244);
x_275 = lean_st_ref_set(x_7, x_274, x_236);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_276);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_278 = lean_ctor_get(x_18, 0);
lean_inc(x_278);
lean_dec(x_18);
x_279 = lean_ctor_get(x_19, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_19, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_19, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_19, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_19, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_19, 5);
lean_inc(x_284);
x_285 = lean_ctor_get(x_19, 6);
lean_inc(x_285);
x_286 = lean_ctor_get(x_19, 7);
lean_inc(x_286);
x_287 = lean_ctor_get(x_19, 8);
lean_inc(x_287);
x_288 = lean_ctor_get(x_19, 9);
lean_inc(x_288);
x_289 = lean_ctor_get(x_19, 10);
lean_inc(x_289);
x_290 = lean_ctor_get(x_19, 11);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_292 = lean_ctor_get(x_19, 12);
lean_inc(x_292);
x_293 = lean_ctor_get(x_19, 13);
lean_inc(x_293);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_294 = x_19;
} else {
 lean_dec_ref(x_19);
 x_294 = lean_box(0);
}
x_295 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_296 = l_Lean_PersistentArray_set___rarg(x_289, x_1, x_295);
if (lean_is_scalar(x_294)) {
 x_297 = lean_alloc_ctor(0, 14, 1);
} else {
 x_297 = x_294;
}
lean_ctor_set(x_297, 0, x_279);
lean_ctor_set(x_297, 1, x_280);
lean_ctor_set(x_297, 2, x_281);
lean_ctor_set(x_297, 3, x_282);
lean_ctor_set(x_297, 4, x_283);
lean_ctor_set(x_297, 5, x_284);
lean_ctor_set(x_297, 6, x_285);
lean_ctor_set(x_297, 7, x_286);
lean_ctor_set(x_297, 8, x_287);
lean_ctor_set(x_297, 9, x_288);
lean_ctor_set(x_297, 10, x_296);
lean_ctor_set(x_297, 11, x_290);
lean_ctor_set(x_297, 12, x_292);
lean_ctor_set(x_297, 13, x_293);
lean_ctor_set_uint8(x_297, sizeof(void*)*14, x_291);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_278);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_17, 13, x_298);
x_299 = lean_st_ref_set(x_7, x_17, x_20);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
x_301 = l_Int_Linear_Poly_eval_x3f(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_300);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_4);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_3);
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_306 = x_301;
} else {
 lean_dec_ref(x_301);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_302, 0);
lean_inc(x_307);
lean_dec(x_302);
x_308 = l_Std_Internal_Rat_neg(x_307);
x_309 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_306)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_306;
}
lean_ctor_set(x_310, 0, x_4);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_Std_Internal_Rat_inv(x_310);
x_312 = l_Std_Internal_Rat_mul(x_308, x_311);
lean_dec(x_311);
lean_dec(x_308);
lean_inc(x_312);
x_313 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_312, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_305);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_st_ref_take(x_7, x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_316, 13);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
lean_dec(x_315);
x_320 = lean_ctor_get(x_316, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_316, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 2);
lean_inc(x_322);
x_323 = lean_ctor_get(x_316, 3);
lean_inc(x_323);
x_324 = lean_ctor_get(x_316, 4);
lean_inc(x_324);
x_325 = lean_ctor_get(x_316, 5);
lean_inc(x_325);
x_326 = lean_ctor_get(x_316, 6);
lean_inc(x_326);
x_327 = lean_ctor_get_uint8(x_316, sizeof(void*)*15);
x_328 = lean_ctor_get(x_316, 7);
lean_inc(x_328);
x_329 = lean_ctor_get(x_316, 8);
lean_inc(x_329);
x_330 = lean_ctor_get(x_316, 9);
lean_inc(x_330);
x_331 = lean_ctor_get(x_316, 10);
lean_inc(x_331);
x_332 = lean_ctor_get(x_316, 11);
lean_inc(x_332);
x_333 = lean_ctor_get(x_316, 12);
lean_inc(x_333);
x_334 = lean_ctor_get(x_316, 14);
lean_inc(x_334);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 lean_ctor_release(x_316, 2);
 lean_ctor_release(x_316, 3);
 lean_ctor_release(x_316, 4);
 lean_ctor_release(x_316, 5);
 lean_ctor_release(x_316, 6);
 lean_ctor_release(x_316, 7);
 lean_ctor_release(x_316, 8);
 lean_ctor_release(x_316, 9);
 lean_ctor_release(x_316, 10);
 lean_ctor_release(x_316, 11);
 lean_ctor_release(x_316, 12);
 lean_ctor_release(x_316, 13);
 lean_ctor_release(x_316, 14);
 x_335 = x_316;
} else {
 lean_dec_ref(x_316);
 x_335 = lean_box(0);
}
x_336 = lean_ctor_get(x_317, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_337 = x_317;
} else {
 lean_dec_ref(x_317);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_318, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_318, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_318, 2);
lean_inc(x_340);
x_341 = lean_ctor_get(x_318, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_318, 4);
lean_inc(x_342);
x_343 = lean_ctor_get(x_318, 5);
lean_inc(x_343);
x_344 = lean_ctor_get(x_318, 6);
lean_inc(x_344);
x_345 = lean_ctor_get(x_318, 7);
lean_inc(x_345);
x_346 = lean_ctor_get(x_318, 8);
lean_inc(x_346);
x_347 = lean_ctor_get(x_318, 9);
lean_inc(x_347);
x_348 = lean_ctor_get(x_318, 10);
lean_inc(x_348);
x_349 = lean_ctor_get(x_318, 11);
lean_inc(x_349);
x_350 = lean_ctor_get_uint8(x_318, sizeof(void*)*14);
x_351 = lean_ctor_get(x_318, 12);
lean_inc(x_351);
x_352 = lean_ctor_get(x_318, 13);
lean_inc(x_352);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 lean_ctor_release(x_318, 2);
 lean_ctor_release(x_318, 3);
 lean_ctor_release(x_318, 4);
 lean_ctor_release(x_318, 5);
 lean_ctor_release(x_318, 6);
 lean_ctor_release(x_318, 7);
 lean_ctor_release(x_318, 8);
 lean_ctor_release(x_318, 9);
 lean_ctor_release(x_318, 10);
 lean_ctor_release(x_318, 11);
 lean_ctor_release(x_318, 12);
 lean_ctor_release(x_318, 13);
 x_353 = x_318;
} else {
 lean_dec_ref(x_318);
 x_353 = lean_box(0);
}
x_354 = l_Lean_PersistentArray_set___rarg(x_348, x_1, x_312);
if (lean_is_scalar(x_353)) {
 x_355 = lean_alloc_ctor(0, 14, 1);
} else {
 x_355 = x_353;
}
lean_ctor_set(x_355, 0, x_338);
lean_ctor_set(x_355, 1, x_339);
lean_ctor_set(x_355, 2, x_340);
lean_ctor_set(x_355, 3, x_341);
lean_ctor_set(x_355, 4, x_342);
lean_ctor_set(x_355, 5, x_343);
lean_ctor_set(x_355, 6, x_344);
lean_ctor_set(x_355, 7, x_345);
lean_ctor_set(x_355, 8, x_346);
lean_ctor_set(x_355, 9, x_347);
lean_ctor_set(x_355, 10, x_354);
lean_ctor_set(x_355, 11, x_349);
lean_ctor_set(x_355, 12, x_351);
lean_ctor_set(x_355, 13, x_352);
lean_ctor_set_uint8(x_355, sizeof(void*)*14, x_350);
if (lean_is_scalar(x_337)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_337;
}
lean_ctor_set(x_356, 0, x_336);
lean_ctor_set(x_356, 1, x_355);
if (lean_is_scalar(x_335)) {
 x_357 = lean_alloc_ctor(0, 15, 1);
} else {
 x_357 = x_335;
}
lean_ctor_set(x_357, 0, x_320);
lean_ctor_set(x_357, 1, x_321);
lean_ctor_set(x_357, 2, x_322);
lean_ctor_set(x_357, 3, x_323);
lean_ctor_set(x_357, 4, x_324);
lean_ctor_set(x_357, 5, x_325);
lean_ctor_set(x_357, 6, x_326);
lean_ctor_set(x_357, 7, x_328);
lean_ctor_set(x_357, 8, x_329);
lean_ctor_set(x_357, 9, x_330);
lean_ctor_set(x_357, 10, x_331);
lean_ctor_set(x_357, 11, x_332);
lean_ctor_set(x_357, 12, x_333);
lean_ctor_set(x_357, 13, x_356);
lean_ctor_set(x_357, 14, x_334);
lean_ctor_set_uint8(x_357, sizeof(void*)*15, x_327);
x_358 = lean_st_ref_set(x_7, x_357, x_319);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_360 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_359);
return x_360;
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_361 = lean_ctor_get(x_17, 0);
x_362 = lean_ctor_get(x_17, 1);
x_363 = lean_ctor_get(x_17, 2);
x_364 = lean_ctor_get(x_17, 3);
x_365 = lean_ctor_get(x_17, 4);
x_366 = lean_ctor_get(x_17, 5);
x_367 = lean_ctor_get(x_17, 6);
x_368 = lean_ctor_get_uint8(x_17, sizeof(void*)*15);
x_369 = lean_ctor_get(x_17, 7);
x_370 = lean_ctor_get(x_17, 8);
x_371 = lean_ctor_get(x_17, 9);
x_372 = lean_ctor_get(x_17, 10);
x_373 = lean_ctor_get(x_17, 11);
x_374 = lean_ctor_get(x_17, 12);
x_375 = lean_ctor_get(x_17, 14);
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_17);
x_376 = lean_ctor_get(x_18, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_377 = x_18;
} else {
 lean_dec_ref(x_18);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_19, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_19, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_19, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_19, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_19, 4);
lean_inc(x_382);
x_383 = lean_ctor_get(x_19, 5);
lean_inc(x_383);
x_384 = lean_ctor_get(x_19, 6);
lean_inc(x_384);
x_385 = lean_ctor_get(x_19, 7);
lean_inc(x_385);
x_386 = lean_ctor_get(x_19, 8);
lean_inc(x_386);
x_387 = lean_ctor_get(x_19, 9);
lean_inc(x_387);
x_388 = lean_ctor_get(x_19, 10);
lean_inc(x_388);
x_389 = lean_ctor_get(x_19, 11);
lean_inc(x_389);
x_390 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_391 = lean_ctor_get(x_19, 12);
lean_inc(x_391);
x_392 = lean_ctor_get(x_19, 13);
lean_inc(x_392);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_393 = x_19;
} else {
 lean_dec_ref(x_19);
 x_393 = lean_box(0);
}
x_394 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1;
x_395 = l_Lean_PersistentArray_set___rarg(x_388, x_1, x_394);
if (lean_is_scalar(x_393)) {
 x_396 = lean_alloc_ctor(0, 14, 1);
} else {
 x_396 = x_393;
}
lean_ctor_set(x_396, 0, x_378);
lean_ctor_set(x_396, 1, x_379);
lean_ctor_set(x_396, 2, x_380);
lean_ctor_set(x_396, 3, x_381);
lean_ctor_set(x_396, 4, x_382);
lean_ctor_set(x_396, 5, x_383);
lean_ctor_set(x_396, 6, x_384);
lean_ctor_set(x_396, 7, x_385);
lean_ctor_set(x_396, 8, x_386);
lean_ctor_set(x_396, 9, x_387);
lean_ctor_set(x_396, 10, x_395);
lean_ctor_set(x_396, 11, x_389);
lean_ctor_set(x_396, 12, x_391);
lean_ctor_set(x_396, 13, x_392);
lean_ctor_set_uint8(x_396, sizeof(void*)*14, x_390);
if (lean_is_scalar(x_377)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_377;
}
lean_ctor_set(x_397, 0, x_376);
lean_ctor_set(x_397, 1, x_396);
x_398 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_398, 0, x_361);
lean_ctor_set(x_398, 1, x_362);
lean_ctor_set(x_398, 2, x_363);
lean_ctor_set(x_398, 3, x_364);
lean_ctor_set(x_398, 4, x_365);
lean_ctor_set(x_398, 5, x_366);
lean_ctor_set(x_398, 6, x_367);
lean_ctor_set(x_398, 7, x_369);
lean_ctor_set(x_398, 8, x_370);
lean_ctor_set(x_398, 9, x_371);
lean_ctor_set(x_398, 10, x_372);
lean_ctor_set(x_398, 11, x_373);
lean_ctor_set(x_398, 12, x_374);
lean_ctor_set(x_398, 13, x_397);
lean_ctor_set(x_398, 14, x_375);
lean_ctor_set_uint8(x_398, sizeof(void*)*15, x_368);
x_399 = lean_st_ref_set(x_7, x_398, x_20);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = l_Int_Linear_Poly_eval_x3f(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_4);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_403);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_3);
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_406 = x_401;
} else {
 lean_dec_ref(x_401);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_402, 0);
lean_inc(x_407);
lean_dec(x_402);
x_408 = l_Std_Internal_Rat_neg(x_407);
x_409 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_406)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_406;
}
lean_ctor_set(x_410, 0, x_4);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Std_Internal_Rat_inv(x_410);
x_412 = l_Std_Internal_Rat_mul(x_408, x_411);
lean_dec(x_411);
lean_dec(x_408);
lean_inc(x_412);
x_413 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment(x_1, x_412, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_405);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_st_ref_take(x_7, x_414);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 13);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
lean_dec(x_415);
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_416, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_416, 4);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 5);
lean_inc(x_425);
x_426 = lean_ctor_get(x_416, 6);
lean_inc(x_426);
x_427 = lean_ctor_get_uint8(x_416, sizeof(void*)*15);
x_428 = lean_ctor_get(x_416, 7);
lean_inc(x_428);
x_429 = lean_ctor_get(x_416, 8);
lean_inc(x_429);
x_430 = lean_ctor_get(x_416, 9);
lean_inc(x_430);
x_431 = lean_ctor_get(x_416, 10);
lean_inc(x_431);
x_432 = lean_ctor_get(x_416, 11);
lean_inc(x_432);
x_433 = lean_ctor_get(x_416, 12);
lean_inc(x_433);
x_434 = lean_ctor_get(x_416, 14);
lean_inc(x_434);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 lean_ctor_release(x_416, 6);
 lean_ctor_release(x_416, 7);
 lean_ctor_release(x_416, 8);
 lean_ctor_release(x_416, 9);
 lean_ctor_release(x_416, 10);
 lean_ctor_release(x_416, 11);
 lean_ctor_release(x_416, 12);
 lean_ctor_release(x_416, 13);
 lean_ctor_release(x_416, 14);
 x_435 = x_416;
} else {
 lean_dec_ref(x_416);
 x_435 = lean_box(0);
}
x_436 = lean_ctor_get(x_417, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_437 = x_417;
} else {
 lean_dec_ref(x_417);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_418, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_418, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_418, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_418, 3);
lean_inc(x_441);
x_442 = lean_ctor_get(x_418, 4);
lean_inc(x_442);
x_443 = lean_ctor_get(x_418, 5);
lean_inc(x_443);
x_444 = lean_ctor_get(x_418, 6);
lean_inc(x_444);
x_445 = lean_ctor_get(x_418, 7);
lean_inc(x_445);
x_446 = lean_ctor_get(x_418, 8);
lean_inc(x_446);
x_447 = lean_ctor_get(x_418, 9);
lean_inc(x_447);
x_448 = lean_ctor_get(x_418, 10);
lean_inc(x_448);
x_449 = lean_ctor_get(x_418, 11);
lean_inc(x_449);
x_450 = lean_ctor_get_uint8(x_418, sizeof(void*)*14);
x_451 = lean_ctor_get(x_418, 12);
lean_inc(x_451);
x_452 = lean_ctor_get(x_418, 13);
lean_inc(x_452);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 lean_ctor_release(x_418, 4);
 lean_ctor_release(x_418, 5);
 lean_ctor_release(x_418, 6);
 lean_ctor_release(x_418, 7);
 lean_ctor_release(x_418, 8);
 lean_ctor_release(x_418, 9);
 lean_ctor_release(x_418, 10);
 lean_ctor_release(x_418, 11);
 lean_ctor_release(x_418, 12);
 lean_ctor_release(x_418, 13);
 x_453 = x_418;
} else {
 lean_dec_ref(x_418);
 x_453 = lean_box(0);
}
x_454 = l_Lean_PersistentArray_set___rarg(x_448, x_1, x_412);
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(0, 14, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_438);
lean_ctor_set(x_455, 1, x_439);
lean_ctor_set(x_455, 2, x_440);
lean_ctor_set(x_455, 3, x_441);
lean_ctor_set(x_455, 4, x_442);
lean_ctor_set(x_455, 5, x_443);
lean_ctor_set(x_455, 6, x_444);
lean_ctor_set(x_455, 7, x_445);
lean_ctor_set(x_455, 8, x_446);
lean_ctor_set(x_455, 9, x_447);
lean_ctor_set(x_455, 10, x_454);
lean_ctor_set(x_455, 11, x_449);
lean_ctor_set(x_455, 12, x_451);
lean_ctor_set(x_455, 13, x_452);
lean_ctor_set_uint8(x_455, sizeof(void*)*14, x_450);
if (lean_is_scalar(x_437)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_437;
}
lean_ctor_set(x_456, 0, x_436);
lean_ctor_set(x_456, 1, x_455);
if (lean_is_scalar(x_435)) {
 x_457 = lean_alloc_ctor(0, 15, 1);
} else {
 x_457 = x_435;
}
lean_ctor_set(x_457, 0, x_420);
lean_ctor_set(x_457, 1, x_421);
lean_ctor_set(x_457, 2, x_422);
lean_ctor_set(x_457, 3, x_423);
lean_ctor_set(x_457, 4, x_424);
lean_ctor_set(x_457, 5, x_425);
lean_ctor_set(x_457, 6, x_426);
lean_ctor_set(x_457, 7, x_428);
lean_ctor_set(x_457, 8, x_429);
lean_ctor_set(x_457, 9, x_430);
lean_ctor_set(x_457, 10, x_431);
lean_ctor_set(x_457, 11, x_432);
lean_ctor_set(x_457, 12, x_433);
lean_ctor_set(x_457, 13, x_456);
lean_ctor_set(x_457, 14, x_434);
lean_ctor_set_uint8(x_457, sizeof(void*)*15, x_427);
x_458 = lean_st_ref_set(x_7, x_457, x_419);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
lean_dec(x_458);
x_460 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_459);
return x_460;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, eliminated variable must have equation associated with it", 81, 81);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = lean_ctor_get(x_16, 6);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_13, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = l_outOfBounds___rarg(x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2;
x_37 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_18 = x_38;
goto block_30;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_PersistentArray_get_x21___rarg(x_31, x_32, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2;
x_41 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_18 = x_42;
goto block_30;
}
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Int_Linear_Poly_coeff(x_19, x_13);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_22 = lean_int_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1(x_13, x_19, x_18, x_20, x_14, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_19);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 7);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_14);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1;
x_15 = lean_box(0);
x_16 = lean_apply_10(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_5, x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_20, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_8, 0, x_28);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_4);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_41);
x_42 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_20, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
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
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_17 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_4);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_36);
x_52 = l_Std_Internal_Rat_neg(x_38);
x_53 = l_Std_Internal_Rat_inv(x_52);
x_54 = l_Std_Internal_Rat_mul(x_50, x_53);
lean_dec(x_53);
lean_dec(x_50);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_39, 0, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_39);
x_22 = x_56;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_free_object(x_39);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
lean_inc(x_54);
x_61 = l_Std_Internal_Rat_lt(x_59, x_54);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_57);
lean_dec(x_54);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_20, 0);
lean_dec(x_64);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_20);
x_22 = x_65;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_20);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
lean_inc(x_54);
x_69 = l_Std_Internal_Rat_lt(x_68, x_54);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_19);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_22 = x_70;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_71 = x_20;
} else {
 lean_dec_ref(x_20);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_19);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_22 = x_74;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
lean_dec(x_39);
x_76 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_76);
lean_ctor_set(x_38, 0, x_36);
x_77 = l_Std_Internal_Rat_neg(x_38);
x_78 = l_Std_Internal_Rat_inv(x_77);
x_79 = l_Std_Internal_Rat_mul(x_75, x_78);
lean_dec(x_78);
lean_dec(x_75);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_22 = x_82;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_20, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
lean_inc(x_79);
x_86 = l_Std_Internal_Rat_lt(x_84, x_79);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_19);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_20);
x_22 = x_87;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_88 = x_20;
} else {
 lean_dec_ref(x_20);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_22 = x_91;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
lean_dec(x_38);
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_94 = x_39;
} else {
 lean_dec_ref(x_39);
 x_94 = lean_box(0);
}
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_36);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Std_Internal_Rat_neg(x_96);
x_98 = l_Std_Internal_Rat_inv(x_97);
x_99 = l_Std_Internal_Rat_mul(x_93, x_98);
lean_dec(x_98);
lean_dec(x_93);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_94);
x_103 = lean_ctor_get(x_20, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
lean_inc(x_99);
x_106 = l_Std_Internal_Rat_lt(x_104, x_99);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_20);
x_22 = x_107;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_108 = x_20;
} else {
 lean_dec_ref(x_20);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_19);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_22 = x_111;
x_23 = x_92;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(x_1, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_36);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(x_36, x_37, x_38, x_36, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_46, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_36);
x_52 = l_Std_Internal_Rat_neg(x_38);
x_53 = l_Std_Internal_Rat_inv(x_52);
x_54 = l_Std_Internal_Rat_mul(x_50, x_53);
lean_dec(x_53);
lean_dec(x_50);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_39, 0, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_39);
x_22 = x_56;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_free_object(x_39);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
lean_inc(x_54);
x_61 = l_Std_Internal_Rat_lt(x_59, x_54);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_57);
lean_dec(x_54);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_20, 0);
lean_dec(x_64);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_20);
x_22 = x_65;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_20);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
lean_inc(x_54);
x_69 = l_Std_Internal_Rat_lt(x_68, x_54);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_19);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_22 = x_70;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_71 = x_20;
} else {
 lean_dec_ref(x_20);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_19);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_22 = x_74;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
lean_dec(x_39);
x_76 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_76);
lean_ctor_set(x_38, 0, x_36);
x_77 = l_Std_Internal_Rat_neg(x_38);
x_78 = l_Std_Internal_Rat_inv(x_77);
x_79 = l_Std_Internal_Rat_mul(x_75, x_78);
lean_dec(x_78);
lean_dec(x_75);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_22 = x_82;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_20, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
lean_inc(x_79);
x_86 = l_Std_Internal_Rat_lt(x_84, x_79);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_19);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_20);
x_22 = x_87;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_88 = x_20;
} else {
 lean_dec_ref(x_20);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_22 = x_91;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
lean_dec(x_38);
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_94 = x_39;
} else {
 lean_dec_ref(x_39);
 x_94 = lean_box(0);
}
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_36);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Std_Internal_Rat_neg(x_96);
x_98 = l_Std_Internal_Rat_inv(x_97);
x_99 = l_Std_Internal_Rat_mul(x_93, x_98);
lean_dec(x_98);
lean_dec(x_93);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_94);
x_103 = lean_ctor_get(x_20, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
lean_inc(x_99);
x_106 = l_Std_Internal_Rat_lt(x_104, x_99);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_20);
x_22 = x_107;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_108 = x_20;
} else {
 lean_dec_ref(x_20);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_19);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_22 = x_111;
x_23 = x_92;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(x_23, x_24, x_25, x_24, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_19 = l_outOfBounds___rarg(x_18);
x_20 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_19, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_30 = l_Lean_PersistentArray_get_x21___rarg(x_29, x_15, x_1);
x_31 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_30, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3___boxed(lean_object** _args) {
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
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__5(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_5, x_7);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_20, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_8, 0, x_28);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_8, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_4);
x_34 = 1;
x_35 = lean_usize_add(x_7, x_34);
x_7 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_22);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
lean_inc(x_41);
x_42 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_20, x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
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
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_17 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_4);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = l_Std_Internal_Rat_neg(x_50);
x_52 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_52);
lean_ctor_set(x_38, 0, x_36);
x_53 = l_Std_Internal_Rat_inv(x_38);
x_54 = l_Std_Internal_Rat_mul(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_39, 0, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_39);
x_22 = x_56;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_free_object(x_39);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
lean_inc(x_54);
x_61 = l_Std_Internal_Rat_lt(x_54, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_57);
lean_dec(x_54);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_20, 0);
lean_dec(x_64);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_20);
x_22 = x_65;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_20);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
lean_inc(x_54);
x_69 = l_Std_Internal_Rat_lt(x_54, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_19);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_22 = x_70;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_71 = x_20;
} else {
 lean_dec_ref(x_20);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_19);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_22 = x_74;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
lean_dec(x_39);
x_76 = l_Std_Internal_Rat_neg(x_75);
x_77 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_77);
lean_ctor_set(x_38, 0, x_36);
x_78 = l_Std_Internal_Rat_inv(x_38);
x_79 = l_Std_Internal_Rat_mul(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_22 = x_82;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_20, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
lean_inc(x_79);
x_86 = l_Std_Internal_Rat_lt(x_79, x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_19);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_20);
x_22 = x_87;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_88 = x_20;
} else {
 lean_dec_ref(x_20);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_22 = x_91;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
lean_dec(x_38);
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_94 = x_39;
} else {
 lean_dec_ref(x_39);
 x_94 = lean_box(0);
}
x_95 = l_Std_Internal_Rat_neg(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_36);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Std_Internal_Rat_inv(x_97);
x_99 = l_Std_Internal_Rat_mul(x_95, x_98);
lean_dec(x_98);
lean_dec(x_95);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_94);
x_103 = lean_ctor_get(x_20, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
lean_inc(x_99);
x_106 = l_Std_Internal_Rat_lt(x_99, x_104);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_20);
x_22 = x_107;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_108 = x_20;
} else {
 lean_dec_ref(x_20);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_19);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_22 = x_111;
x_23 = x_92;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(x_1, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_36);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(x_36, x_37, x_38, x_36, x_40, x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___spec__2___lambda__1(x_46, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_51);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; 
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Int_Linear_Poly_eval_x3f(x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = l_Std_Internal_Rat_neg(x_50);
x_52 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_52);
lean_ctor_set(x_38, 0, x_36);
x_53 = l_Std_Internal_Rat_inv(x_38);
x_54 = l_Std_Internal_Rat_mul(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_39, 0, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_39);
x_22 = x_56;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_free_object(x_39);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
lean_inc(x_54);
x_61 = l_Std_Internal_Rat_lt(x_54, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_57);
lean_dec(x_54);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_20);
x_22 = x_62;
x_23 = x_47;
goto block_29;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_20, 0);
lean_dec(x_64);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_20);
x_22 = x_65;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_20);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 0, x_54);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_22 = x_67;
x_23 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
lean_inc(x_54);
x_69 = l_Std_Internal_Rat_lt(x_54, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_19);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_22 = x_70;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_71 = x_20;
} else {
 lean_dec_ref(x_20);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_19);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_22 = x_74;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
lean_dec(x_39);
x_76 = l_Std_Internal_Rat_neg(x_75);
x_77 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_38, 1, x_77);
lean_ctor_set(x_38, 0, x_36);
x_78 = l_Std_Internal_Rat_inv(x_38);
x_79 = l_Std_Internal_Rat_mul(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_19);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_22 = x_82;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_20, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
lean_inc(x_79);
x_86 = l_Std_Internal_Rat_lt(x_79, x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_19);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_20);
x_22 = x_87;
x_23 = x_47;
goto block_29;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_88 = x_20;
} else {
 lean_dec_ref(x_20);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_19);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_22 = x_91;
x_23 = x_47;
goto block_29;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_38, 1);
lean_inc(x_92);
lean_dec(x_38);
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_94 = x_39;
} else {
 lean_dec_ref(x_39);
 x_94 = lean_box(0);
}
x_95 = l_Std_Internal_Rat_neg(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_36);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Std_Internal_Rat_inv(x_97);
x_99 = l_Std_Internal_Rat_mul(x_95, x_98);
lean_dec(x_98);
lean_dec(x_95);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_19);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_22 = x_102;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_94);
x_103 = lean_ctor_get(x_20, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
lean_inc(x_99);
x_106 = l_Std_Internal_Rat_lt(x_99, x_104);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_20);
x_22 = x_107;
x_23 = x_92;
goto block_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_108 = x_20;
} else {
 lean_dec_ref(x_20);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_19);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_22 = x_111;
x_23 = x_92;
goto block_29;
}
}
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(x_23, x_24, x_25, x_24, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_19 = l_outOfBounds___rarg(x_18);
x_20 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_19, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_30 = l_Lean_PersistentArray_get_x21___rarg(x_29, x_15, x_1);
x_31 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_30, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3___boxed(lean_object** _args) {
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
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__5(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_7, x_6);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_uget(x_5, x_7);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 0);
lean_dec(x_25);
lean_inc(x_24);
x_26 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(x_1, x_22, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set(x_26, 0, x_8);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_8, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_35);
lean_ctor_set(x_8, 0, x_4);
x_36 = 1;
x_37 = lean_usize_add(x_7, x_36);
x_7 = x_37;
x_19 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_dec(x_8);
lean_inc(x_43);
x_44 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(x_1, x_22, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_22);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
lean_dec(x_43);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = 1;
x_55 = lean_usize_add(x_7, x_54);
x_7 = x_55;
x_8 = x_53;
x_19 = x_51;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_43);
lean_dec(x_4);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_40; 
x_21 = lean_array_uget(x_4, x_6);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_30 = x_7;
} else {
 lean_dec_ref(x_7);
 x_30 = lean_box(0);
}
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___rarg(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 2);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Int_Linear_Poly_eval_x3f(x_47, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___rarg(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_48, 1);
x_58 = lean_ctor_get(x_48, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_dec(x_69);
x_70 = lean_int_emod(x_68, x_46);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_72 = lean_int_dec_eq(x_70, x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_free_object(x_60);
lean_dec(x_68);
lean_free_object(x_61);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_60, 1, x_73);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_46);
x_74 = l_Std_Internal_Rat_inv(x_61);
x_75 = l_Std_Internal_Rat_mul(x_60, x_74);
lean_dec(x_74);
lean_dec(x_60);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_75);
x_76 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_76);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_int_emod(x_77, x_46);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_80 = lean_int_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_dec(x_77);
lean_free_object(x_61);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_61, 1, x_81);
lean_ctor_set(x_61, 0, x_46);
x_83 = l_Std_Internal_Rat_inv(x_61);
x_84 = l_Std_Internal_Rat_mul(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_84);
x_85 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_85);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_dec(x_61);
x_87 = lean_ctor_get(x_60, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_88 = x_60;
} else {
 lean_dec_ref(x_60);
 x_88 = lean_box(0);
}
x_89 = lean_int_emod(x_87, x_46);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_91 = lean_int_dec_eq(x_89, x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_86;
goto block_39;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_46);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Std_Internal_Rat_inv(x_94);
x_96 = l_Std_Internal_Rat_mul(x_93, x_95);
lean_dec(x_95);
lean_dec(x_93);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_96);
x_97 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_97);
x_31 = x_49;
x_32 = x_86;
goto block_39;
}
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_61);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_61, 1);
x_100 = lean_ctor_get(x_61, 0);
lean_dec(x_100);
x_101 = l_Std_Internal_Rat_neg(x_60);
x_102 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_61, 1, x_102);
lean_ctor_set(x_61, 0, x_46);
x_103 = l_Std_Internal_Rat_inv(x_61);
x_104 = l_Std_Internal_Rat_mul(x_101, x_103);
lean_dec(x_103);
lean_dec(x_101);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_104);
x_105 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_105);
x_31 = x_49;
x_32 = x_99;
goto block_39;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_61, 1);
lean_inc(x_106);
lean_dec(x_61);
x_107 = l_Std_Internal_Rat_neg(x_60);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_46);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Std_Internal_Rat_inv(x_109);
x_111 = l_Std_Internal_Rat_mul(x_107, x_110);
lean_dec(x_110);
lean_dec(x_107);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_111);
x_112 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_112);
x_31 = x_49;
x_32 = x_106;
goto block_39;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_49, 0);
lean_inc(x_113);
lean_dec(x_49);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_57);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
x_121 = lean_int_emod(x_119, x_46);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_123 = lean_int_dec_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_29);
x_31 = x_124;
x_32 = x_117;
goto block_39;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_120;
}
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_118)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_118;
}
lean_ctor_set(x_127, 0, x_46);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Std_Internal_Rat_inv(x_127);
x_129 = l_Std_Internal_Rat_mul(x_126, x_128);
lean_dec(x_128);
lean_dec(x_126);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_129);
x_130 = lean_array_push(x_29, x_48);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_31 = x_131;
x_32 = x_117;
goto block_39;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_114, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_133 = x_114;
} else {
 lean_dec_ref(x_114);
 x_133 = lean_box(0);
}
x_134 = l_Std_Internal_Rat_neg(x_113);
x_135 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_46);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Std_Internal_Rat_inv(x_136);
x_138 = l_Std_Internal_Rat_mul(x_134, x_137);
lean_dec(x_137);
lean_dec(x_134);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_138);
x_139 = lean_array_push(x_29, x_48);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_31 = x_140;
x_32 = x_132;
goto block_39;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_48, 1);
lean_inc(x_141);
lean_dec(x_48);
x_142 = lean_ctor_get(x_49, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_143 = x_49;
} else {
 lean_dec_ref(x_49);
 x_143 = lean_box(0);
}
x_144 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_141);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_142, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_150 = x_142;
} else {
 lean_dec_ref(x_142);
 x_150 = lean_box(0);
}
x_151 = lean_int_emod(x_149, x_46);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_153 = lean_int_dec_eq(x_151, x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_46);
lean_dec(x_21);
if (lean_is_scalar(x_143)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_143;
}
lean_ctor_set(x_154, 0, x_29);
x_31 = x_154;
x_32 = x_147;
goto block_39;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_150)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_150;
}
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_46);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Std_Internal_Rat_inv(x_157);
x_159 = l_Std_Internal_Rat_mul(x_156, x_158);
lean_dec(x_158);
lean_dec(x_156);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_21);
x_161 = lean_array_push(x_29, x_160);
if (lean_is_scalar(x_143)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_143;
}
lean_ctor_set(x_162, 0, x_161);
x_31 = x_162;
x_32 = x_147;
goto block_39;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_164 = x_144;
} else {
 lean_dec_ref(x_144);
 x_164 = lean_box(0);
}
x_165 = l_Std_Internal_Rat_neg(x_142);
x_166 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_46);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Std_Internal_Rat_inv(x_167);
x_169 = l_Std_Internal_Rat_mul(x_165, x_168);
lean_dec(x_168);
lean_dec(x_165);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_21);
x_171 = lean_array_push(x_29, x_170);
if (lean_is_scalar(x_143)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_143;
}
lean_ctor_set(x_172, 0, x_171);
x_31 = x_172;
x_32 = x_163;
goto block_39;
}
}
}
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
x_18 = x_23;
goto _start;
}
block_39:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_3);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_31, 0, x_35);
x_22 = x_31;
x_23 = x_32;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_3);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_22 = x_38;
x_23 = x_32;
goto block_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_array_size(x_15);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3(x_1, x_15, x_16, x_17, x_15, x_19, x_20, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_22);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
x_42 = lean_array_size(x_38);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4(x_38, x_39, x_40, x_38, x_42, x_43, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_box(0);
x_50 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1(x_48, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_47);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_45);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_44, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_40; 
x_21 = lean_array_uget(x_4, x_6);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_30 = x_7;
} else {
 lean_dec_ref(x_7);
 x_30 = lean_box(0);
}
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_40);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___rarg(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 2);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Int_Linear_Poly_eval_x3f(x_47, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___rarg(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_48, 1);
x_58 = lean_ctor_get(x_48, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_dec(x_69);
x_70 = lean_int_emod(x_68, x_46);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_72 = lean_int_dec_eq(x_70, x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_free_object(x_60);
lean_dec(x_68);
lean_free_object(x_61);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_60, 1, x_73);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_46);
x_74 = l_Std_Internal_Rat_inv(x_61);
x_75 = l_Std_Internal_Rat_mul(x_60, x_74);
lean_dec(x_74);
lean_dec(x_60);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_75);
x_76 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_76);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_int_emod(x_77, x_46);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_80 = lean_int_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_dec(x_77);
lean_free_object(x_61);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_61, 1, x_81);
lean_ctor_set(x_61, 0, x_46);
x_83 = l_Std_Internal_Rat_inv(x_61);
x_84 = l_Std_Internal_Rat_mul(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_84);
x_85 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_85);
x_31 = x_49;
x_32 = x_65;
goto block_39;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_dec(x_61);
x_87 = lean_ctor_get(x_60, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_88 = x_60;
} else {
 lean_dec_ref(x_60);
 x_88 = lean_box(0);
}
x_89 = lean_int_emod(x_87, x_46);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_91 = lean_int_dec_eq(x_89, x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
lean_ctor_set(x_49, 0, x_29);
x_31 = x_49;
x_32 = x_86;
goto block_39;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_46);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Std_Internal_Rat_inv(x_94);
x_96 = l_Std_Internal_Rat_mul(x_93, x_95);
lean_dec(x_95);
lean_dec(x_93);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_96);
x_97 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_97);
x_31 = x_49;
x_32 = x_86;
goto block_39;
}
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_61);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_61, 1);
x_100 = lean_ctor_get(x_61, 0);
lean_dec(x_100);
x_101 = l_Std_Internal_Rat_neg(x_60);
x_102 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_61, 1, x_102);
lean_ctor_set(x_61, 0, x_46);
x_103 = l_Std_Internal_Rat_inv(x_61);
x_104 = l_Std_Internal_Rat_mul(x_101, x_103);
lean_dec(x_103);
lean_dec(x_101);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_104);
x_105 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_105);
x_31 = x_49;
x_32 = x_99;
goto block_39;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_61, 1);
lean_inc(x_106);
lean_dec(x_61);
x_107 = l_Std_Internal_Rat_neg(x_60);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_46);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Std_Internal_Rat_inv(x_109);
x_111 = l_Std_Internal_Rat_mul(x_107, x_110);
lean_dec(x_110);
lean_dec(x_107);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_111);
x_112 = lean_array_push(x_29, x_48);
lean_ctor_set(x_49, 0, x_112);
x_31 = x_49;
x_32 = x_106;
goto block_39;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_49, 0);
lean_inc(x_113);
lean_dec(x_49);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_57);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
x_121 = lean_int_emod(x_119, x_46);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_123 = lean_int_dec_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_free_object(x_48);
lean_dec(x_46);
lean_dec(x_21);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_29);
x_31 = x_124;
x_32 = x_117;
goto block_39;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_120;
}
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_118)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_118;
}
lean_ctor_set(x_127, 0, x_46);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Std_Internal_Rat_inv(x_127);
x_129 = l_Std_Internal_Rat_mul(x_126, x_128);
lean_dec(x_128);
lean_dec(x_126);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_129);
x_130 = lean_array_push(x_29, x_48);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_31 = x_131;
x_32 = x_117;
goto block_39;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_114, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_133 = x_114;
} else {
 lean_dec_ref(x_114);
 x_133 = lean_box(0);
}
x_134 = l_Std_Internal_Rat_neg(x_113);
x_135 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_46);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Std_Internal_Rat_inv(x_136);
x_138 = l_Std_Internal_Rat_mul(x_134, x_137);
lean_dec(x_137);
lean_dec(x_134);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 0, x_138);
x_139 = lean_array_push(x_29, x_48);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_31 = x_140;
x_32 = x_132;
goto block_39;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_48, 1);
lean_inc(x_141);
lean_dec(x_48);
x_142 = lean_ctor_get(x_49, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_143 = x_49;
} else {
 lean_dec_ref(x_49);
 x_143 = lean_box(0);
}
x_144 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_141);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_142, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_150 = x_142;
} else {
 lean_dec_ref(x_142);
 x_150 = lean_box(0);
}
x_151 = lean_int_emod(x_149, x_46);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_153 = lean_int_dec_eq(x_151, x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_46);
lean_dec(x_21);
if (lean_is_scalar(x_143)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_143;
}
lean_ctor_set(x_154, 0, x_29);
x_31 = x_154;
x_32 = x_147;
goto block_39;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_150)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_150;
}
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_46);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Std_Internal_Rat_inv(x_157);
x_159 = l_Std_Internal_Rat_mul(x_156, x_158);
lean_dec(x_158);
lean_dec(x_156);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_21);
x_161 = lean_array_push(x_29, x_160);
if (lean_is_scalar(x_143)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_143;
}
lean_ctor_set(x_162, 0, x_161);
x_31 = x_162;
x_32 = x_147;
goto block_39;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_164 = x_144;
} else {
 lean_dec_ref(x_144);
 x_164 = lean_box(0);
}
x_165 = l_Std_Internal_Rat_neg(x_142);
x_166 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_46);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Std_Internal_Rat_inv(x_167);
x_169 = l_Std_Internal_Rat_mul(x_165, x_168);
lean_dec(x_168);
lean_dec(x_165);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_21);
x_171 = lean_array_push(x_29, x_170);
if (lean_is_scalar(x_143)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_143;
}
lean_ctor_set(x_172, 0, x_171);
x_31 = x_172;
x_32 = x_163;
goto block_39;
}
}
}
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
x_18 = x_23;
goto _start;
}
block_39:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_3);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_31, 0, x_35);
x_22 = x_31;
x_23 = x_32;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_3);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_22 = x_38;
x_23 = x_32;
goto block_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_15 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(x_2, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_size(x_26);
x_30 = 0;
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5(x_25, x_26, x_27, x_26, x_29, x_30, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_32);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 5);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_20 = l_outOfBounds___rarg(x_19);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_22 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1(x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1;
x_32 = l_Lean_PersistentArray_get_x21___rarg(x_31, x_16, x_1);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_34 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1(x_32, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3___boxed(lean_object** _args) {
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
_start:
{
size_t x_20; size_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__3(x_1, x_2, x_3, x_4, x_5, x_20, x_21, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4___boxed(lean_object** _args) {
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
size_t x_19; size_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__4(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_PersistentArray_forInAux___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5___boxed(lean_object** _args) {
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
size_t x_19; size_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__5(x_1, x_2, x_3, x_4, x_19, x_20, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_PersistentArray_forIn___at_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___spec__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_nat_to_int(x_1);
x_18 = lean_int_ediv(x_2, x_17);
x_19 = lean_int_ediv(x_3, x_17);
x_20 = lean_int_ediv(x_4, x_17);
lean_dec(x_17);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_gcdExt(x_19, x_18);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_dec(x_27);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_29 = lean_int_dec_lt(x_26, x_28);
x_30 = lean_int_neg(x_20);
lean_dec(x_20);
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_int_mul(x_30, x_26);
lean_dec(x_26);
lean_dec(x_30);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_23, 0, x_18);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_int_emod(x_26, x_18);
lean_dec(x_26);
x_34 = lean_int_mul(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_ctor_set(x_23, 1, x_34);
lean_ctor_set(x_23, 0, x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_38 = lean_int_dec_lt(x_36, x_37);
x_39 = lean_int_neg(x_20);
lean_dec(x_20);
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_int_mul(x_39, x_36);
lean_dec(x_36);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 0, x_42);
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_int_emod(x_36, x_18);
lean_dec(x_36);
x_44 = lean_int_mul(x_39, x_43);
lean_dec(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 0, x_46);
return x_21;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_51 = lean_int_dec_lt(x_48, x_50);
x_52 = lean_int_neg(x_20);
lean_dec(x_20);
if (x_51 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_int_mul(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_16);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_int_emod(x_48, x_18);
lean_dec(x_48);
x_58 = lean_int_mul(x_52, x_57);
lean_dec(x_57);
lean_dec(x_52);
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_49;
}
lean_ctor_set(x_59, 0, x_18);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_16);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = l_Int_gcd(x_2, x_3);
lean_inc(x_17);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_emod(x_16, x_18);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_21 = lean_int_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(x_17, x_2, x_3, x_16, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_13);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Int_Linear_Poly_eval_x3f(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2(x_23, x_17, x_15, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_15);
lean_dec(x_17);
lean_dec(x_23);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___lambda__2(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Int_gcd(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_mkDvdCnstr(x_18, x_15, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_21);
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_33);
x_34 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
lean_inc(x_1);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(7, 2, 0);
} else {
 x_44 = x_42;
 lean_ctor_set_tag(x_44, 7);
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_int_sub(x_2, x_3);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Int_Linear_cdiv(x_4, x_5);
lean_dec(x_4);
x_7 = lean_int_mul(x_6, x_5);
lean_dec(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_int_sub(x_2, x_3);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_int_ediv(x_4, x_5);
lean_dec(x_4);
x_7 = lean_int_mul(x_6, x_5);
lean_dec(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 1;
x_16 = lean_usize_add(x_7, x_15);
{
size_t _tmp_6 = x_16;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_int_dec_eq(x_18, x_1);
lean_dec(x_18);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
{
size_t _tmp_6 = x_21;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_10);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3;
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1(x_1, x_2, x_3, x_6, x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = l___private_Std_Internal_Rat_0__Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_37_(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_7, x_13);
{
size_t _tmp_6 = x_14;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1(x_1, x_2, x_3, x_6, x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(x_1, x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues(x_4, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_4);
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_le(x_1, x_2);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_inDiseqValues(x_4, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_7 = lean_int_sub(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(x_1, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_10 = lean_int_add(x_4, x_9);
lean_dec(x_4);
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(x_1, x_10);
lean_dec(x_10);
x_12 = lean_int_dec_lt(x_2, x_11);
if (x_12 == 0)
{
lean_free_object(x_5);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_16 = lean_int_add(x_4, x_15);
lean_dec(x_4);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(x_1, x_16);
lean_dec(x_16);
x_18 = lean_int_dec_lt(x_2, x_17);
if (x_18 == 0)
{
lean_dec(x_14);
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_ge(x_1, x_2);
x_6 = lean_int_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_findIntVal_go(x_1, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findIntVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_findIntVal(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2;
x_2 = l_Std_Internal_Rat_inv(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = l_Std_Internal_Rat_add(x_1, x_2);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3;
x_6 = l_Std_Internal_Rat_mul(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_dec(x_7);
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_findRatVal(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_13);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___rarg(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_nat_abs(x_19);
lean_dec(x_19);
x_22 = lean_nat_to_int(x_21);
x_23 = l_Int_Linear_Poly_mul(x_18, x_22);
lean_dec(x_22);
x_24 = lean_nat_abs(x_17);
lean_dec(x_17);
x_25 = lean_nat_to_int(x_24);
x_26 = l_Int_Linear_Poly_mul(x_20, x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(100000000u);
x_28 = l_Int_Linear_Poly_combine_x27(x_27, x_23, x_26);
lean_inc(x_28);
x_29 = l_Int_Linear_Poly_satisfiedLe(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = 0;
x_34 = lean_unbox(x_31);
lean_dec(x_31);
x_35 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_34, x_33);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = 0;
x_37 = lean_box(x_36);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_29);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_28, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = 0;
x_58 = lean_unbox(x_55);
lean_dec(x_55);
x_59 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_58, x_57);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = 0;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_28, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = 1;
x_71 = lean_box(x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_2);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_30);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_26);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_22);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_22);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
lean_inc(x_2);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_52;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_50);
lean_ctor_set(x_13, 0, x_56);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_13);
lean_ctor_set(x_57, 1, x_53);
x_58 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_dec(x_13);
lean_inc(x_1);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
lean_inc(x_2);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(7, 2, 0);
} else {
 x_72 = x_70;
 lean_ctor_set_tag(x_72, 7);
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_66;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
x_77 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_12, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
lean_dec(x_78);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_mkCnstrId(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_13, x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_20);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Int_Linear_Poly_leadCoeff(x_14);
lean_dec(x_14);
x_16 = lean_nat_abs(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = l_Int_Linear_Poly_leadCoeff(x_17);
lean_dec(x_17);
x_19 = lean_nat_abs(x_18);
lean_dec(x_18);
x_20 = lean_nat_dec_lt(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_20);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Int_Linear_Poly_leadCoeff(x_15);
lean_dec(x_15);
x_17 = lean_nat_abs(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = l_Int_Linear_Poly_leadCoeff(x_18);
lean_dec(x_18);
x_20 = lean_nat_abs(x_19);
lean_dec(x_19);
x_21 = lean_nat_dec_lt(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_21);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperPred(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cooper-diseq NIY ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 0, x_21);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_17);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_19);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_15);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_31);
lean_ctor_set(x_13, 0, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_27);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_41;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Int_Linear_Poly_updateOccs___spec__1(x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7;
x_14 = lean_panic_fn(x_13, x_1);
x_15 = lean_box(x_2);
x_16 = lean_apply_11(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types___hyg_6_(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 2);
x_14 = l_Lean_isTracingEnabledForCore(x_1, x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types___hyg_6_(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqPoly____x40_Init_Data_Int_Linear___hyg_596_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__9(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__9(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_hashPoly____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types___hyg_6_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
static double _init_l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_11, 5);
x_15 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_12, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_19, 3);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_29 = 0;
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_14);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_14);
x_34 = l_Lean_PersistentArray_push___rarg(x_27, x_18);
lean_ctor_set(x_20, 0, x_34);
x_35 = lean_st_ref_set(x_12, x_19, x_22);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint64_t x_42; lean_object* x_43; double x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get_uint64(x_20, sizeof(void*)*1);
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
lean_dec(x_20);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_45 = 0;
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_44);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_45);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_16);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_14);
lean_ctor_set(x_18, 1, x_49);
lean_ctor_set(x_18, 0, x_14);
x_50 = l_Lean_PersistentArray_push___rarg(x_43, x_18);
x_51 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*1, x_42);
lean_ctor_set(x_19, 3, x_51);
x_52 = lean_st_ref_set(x_12, x_19, x_22);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; double x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
x_59 = lean_ctor_get(x_19, 2);
x_60 = lean_ctor_get(x_19, 4);
x_61 = lean_ctor_get(x_19, 5);
x_62 = lean_ctor_get(x_19, 6);
x_63 = lean_ctor_get(x_19, 7);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_64 = lean_ctor_get_uint64(x_20, sizeof(void*)*1);
x_65 = lean_ctor_get(x_20, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_66 = x_20;
} else {
 lean_dec_ref(x_20);
 x_66 = lean_box(0);
}
x_67 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_68 = 0;
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_70 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_float(x_70, sizeof(void*)*2, x_67);
lean_ctor_set_float(x_70, sizeof(void*)*2 + 8, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 16, x_68);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_72 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_16);
lean_ctor_set(x_72, 2, x_71);
lean_inc(x_14);
lean_ctor_set(x_18, 1, x_72);
lean_ctor_set(x_18, 0, x_14);
x_73 = l_Lean_PersistentArray_push___rarg(x_65, x_18);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 1, 8);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint64(x_74, sizeof(void*)*1, x_64);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_58);
lean_ctor_set(x_75, 2, x_59);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_60);
lean_ctor_set(x_75, 5, x_61);
lean_ctor_set(x_75, 6, x_62);
lean_ctor_set(x_75, 7, x_63);
x_76 = lean_st_ref_set(x_12, x_75, x_22);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; lean_object* x_91; lean_object* x_92; double x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_81 = lean_ctor_get(x_18, 1);
lean_inc(x_81);
lean_dec(x_18);
x_82 = lean_ctor_get(x_19, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_19, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_19, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_19, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_19, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_19, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_19, 7);
lean_inc(x_88);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 x_89 = x_19;
} else {
 lean_dec_ref(x_19);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get_uint64(x_20, sizeof(void*)*1);
x_91 = lean_ctor_get(x_20, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_92 = x_20;
} else {
 lean_dec_ref(x_20);
 x_92 = lean_box(0);
}
x_93 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_94 = 0;
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_96 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set_float(x_96, sizeof(void*)*2, x_93);
lean_ctor_set_float(x_96, sizeof(void*)*2 + 8, x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 16, x_94);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_98 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_16);
lean_ctor_set(x_98, 2, x_97);
lean_inc(x_14);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_14);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_PersistentArray_push___rarg(x_91, x_99);
if (lean_is_scalar(x_92)) {
 x_101 = lean_alloc_ctor(0, 1, 8);
} else {
 x_101 = x_92;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint64(x_101, sizeof(void*)*1, x_90);
if (lean_is_scalar(x_89)) {
 x_102 = lean_alloc_ctor(0, 8, 0);
} else {
 x_102 = x_89;
}
lean_ctor_set(x_102, 0, x_82);
lean_ctor_set(x_102, 1, x_83);
lean_ctor_set(x_102, 2, x_84);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_85);
lean_ctor_set(x_102, 5, x_86);
lean_ctor_set(x_102, 6, x_87);
lean_ctor_set(x_102, 7, x_88);
x_103 = lean_st_ref_set(x_12, x_102, x_81);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("b\n\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Cutsat.Search", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Cutsat.resolveRatDiseq", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5;
x_3 = lean_unsigned_to_nat(313u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_17 = l_Int_Linear_Poly_addConst(x_15, x_16);
x_18 = l_Lean_Expr_fvar___override(x_3);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_17, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict(x_2, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6;
x_28 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 13);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_17, 13);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 13);
lean_inc(x_2);
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(x_26, x_1, x_2);
lean_ctor_set(x_19, 13, x_27);
x_28 = lean_st_ref_set(x_7, x_17, x_20);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(x_5);
x_31 = lean_apply_12(x_3, x_2, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
x_34 = lean_ctor_get(x_19, 2);
x_35 = lean_ctor_get(x_19, 3);
x_36 = lean_ctor_get(x_19, 4);
x_37 = lean_ctor_get(x_19, 5);
x_38 = lean_ctor_get(x_19, 6);
x_39 = lean_ctor_get(x_19, 7);
x_40 = lean_ctor_get(x_19, 8);
x_41 = lean_ctor_get(x_19, 9);
x_42 = lean_ctor_get(x_19, 10);
x_43 = lean_ctor_get(x_19, 11);
x_44 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_45 = lean_ctor_get(x_19, 12);
x_46 = lean_ctor_get(x_19, 13);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
lean_inc(x_2);
x_47 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(x_46, x_1, x_2);
x_48 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_48, 0, x_32);
lean_ctor_set(x_48, 1, x_33);
lean_ctor_set(x_48, 2, x_34);
lean_ctor_set(x_48, 3, x_35);
lean_ctor_set(x_48, 4, x_36);
lean_ctor_set(x_48, 5, x_37);
lean_ctor_set(x_48, 6, x_38);
lean_ctor_set(x_48, 7, x_39);
lean_ctor_set(x_48, 8, x_40);
lean_ctor_set(x_48, 9, x_41);
lean_ctor_set(x_48, 10, x_42);
lean_ctor_set(x_48, 11, x_43);
lean_ctor_set(x_48, 12, x_45);
lean_ctor_set(x_48, 13, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*14, x_44);
lean_ctor_set(x_18, 1, x_48);
x_49 = lean_st_ref_set(x_7, x_17, x_20);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(x_5);
x_52 = lean_apply_12(x_3, x_2, x_51, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_53 = lean_ctor_get(x_18, 0);
lean_inc(x_53);
lean_dec(x_18);
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_19, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_19, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_19, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_19, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 7);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 8);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 9);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 10);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 11);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_67 = lean_ctor_get(x_19, 12);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 13);
lean_inc(x_68);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_69 = x_19;
} else {
 lean_dec_ref(x_19);
 x_69 = lean_box(0);
}
lean_inc(x_2);
x_70 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(x_68, x_1, x_2);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 14, 1);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_55);
lean_ctor_set(x_71, 2, x_56);
lean_ctor_set(x_71, 3, x_57);
lean_ctor_set(x_71, 4, x_58);
lean_ctor_set(x_71, 5, x_59);
lean_ctor_set(x_71, 6, x_60);
lean_ctor_set(x_71, 7, x_61);
lean_ctor_set(x_71, 8, x_62);
lean_ctor_set(x_71, 9, x_63);
lean_ctor_set(x_71, 10, x_64);
lean_ctor_set(x_71, 11, x_65);
lean_ctor_set(x_71, 12, x_67);
lean_ctor_set(x_71, 13, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*14, x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_17, 13, x_72);
x_73 = lean_st_ref_set(x_7, x_17, x_20);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_box(x_5);
x_76 = lean_apply_12(x_3, x_2, x_75, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_77 = lean_ctor_get(x_17, 0);
x_78 = lean_ctor_get(x_17, 1);
x_79 = lean_ctor_get(x_17, 2);
x_80 = lean_ctor_get(x_17, 3);
x_81 = lean_ctor_get(x_17, 4);
x_82 = lean_ctor_get(x_17, 5);
x_83 = lean_ctor_get(x_17, 6);
x_84 = lean_ctor_get_uint8(x_17, sizeof(void*)*15);
x_85 = lean_ctor_get(x_17, 7);
x_86 = lean_ctor_get(x_17, 8);
x_87 = lean_ctor_get(x_17, 9);
x_88 = lean_ctor_get(x_17, 10);
x_89 = lean_ctor_get(x_17, 11);
x_90 = lean_ctor_get(x_17, 12);
x_91 = lean_ctor_get(x_17, 14);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_17);
x_92 = lean_ctor_get(x_18, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_93 = x_18;
} else {
 lean_dec_ref(x_18);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_19, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_19, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_19, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_19, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_19, 5);
lean_inc(x_99);
x_100 = lean_ctor_get(x_19, 6);
lean_inc(x_100);
x_101 = lean_ctor_get(x_19, 7);
lean_inc(x_101);
x_102 = lean_ctor_get(x_19, 8);
lean_inc(x_102);
x_103 = lean_ctor_get(x_19, 9);
lean_inc(x_103);
x_104 = lean_ctor_get(x_19, 10);
lean_inc(x_104);
x_105 = lean_ctor_get(x_19, 11);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_19, sizeof(void*)*14);
x_107 = lean_ctor_get(x_19, 12);
lean_inc(x_107);
x_108 = lean_ctor_get(x_19, 13);
lean_inc(x_108);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 lean_ctor_release(x_19, 9);
 lean_ctor_release(x_19, 10);
 lean_ctor_release(x_19, 11);
 lean_ctor_release(x_19, 12);
 lean_ctor_release(x_19, 13);
 x_109 = x_19;
} else {
 lean_dec_ref(x_19);
 x_109 = lean_box(0);
}
lean_inc(x_2);
x_110 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__6(x_108, x_1, x_2);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 14, 1);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_95);
lean_ctor_set(x_111, 2, x_96);
lean_ctor_set(x_111, 3, x_97);
lean_ctor_set(x_111, 4, x_98);
lean_ctor_set(x_111, 5, x_99);
lean_ctor_set(x_111, 6, x_100);
lean_ctor_set(x_111, 7, x_101);
lean_ctor_set(x_111, 8, x_102);
lean_ctor_set(x_111, 9, x_103);
lean_ctor_set(x_111, 10, x_104);
lean_ctor_set(x_111, 11, x_105);
lean_ctor_set(x_111, 12, x_107);
lean_ctor_set(x_111, 13, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*14, x_106);
if (lean_is_scalar(x_93)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_93;
}
lean_ctor_set(x_112, 0, x_92);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_113, 0, x_77);
lean_ctor_set(x_113, 1, x_78);
lean_ctor_set(x_113, 2, x_79);
lean_ctor_set(x_113, 3, x_80);
lean_ctor_set(x_113, 4, x_81);
lean_ctor_set(x_113, 5, x_82);
lean_ctor_set(x_113, 6, x_83);
lean_ctor_set(x_113, 7, x_85);
lean_ctor_set(x_113, 8, x_86);
lean_ctor_set(x_113, 9, x_87);
lean_ctor_set(x_113, 10, x_88);
lean_ctor_set(x_113, 11, x_89);
lean_ctor_set(x_113, 12, x_90);
lean_ctor_set(x_113, 13, x_112);
lean_ctor_set(x_113, 14, x_91);
lean_ctor_set_uint8(x_113, sizeof(void*)*15, x_84);
x_114 = lean_st_ref_set(x_7, x_113, x_20);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(x_5);
x_117 = lean_apply_12(x_3, x_2, x_116, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
return x_117;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(x_4);
x_16 = lean_apply_12(x_1, x_2, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diseq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2;
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", reusing ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_1);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___boxed), 14, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_1);
x_19 = lean_ctor_get(x_16, 13);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2(x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_1);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_free_object(x_14);
lean_dec(x_2);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_25, x_18, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_41);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_42);
lean_ctor_set(x_28, 0, x_37);
lean_inc(x_25);
x_43 = l_Lean_MessageData_ofName(x_25);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_43);
lean_ctor_set(x_23, 0, x_28);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_41);
lean_ctor_set(x_14, 0, x_23);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_27, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_25, x_18, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_37);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_52);
lean_ctor_set(x_28, 0, x_51);
lean_inc(x_25);
x_53 = l_Lean_MessageData_ofName(x_25);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_53);
lean_ctor_set(x_23, 0, x_28);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_50);
lean_ctor_set(x_14, 0, x_23);
x_54 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_27, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_25, x_18, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_56);
lean_dec(x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_dec(x_28);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_62;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_25);
x_67 = l_Lean_MessageData_ofName(x_25);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_67);
lean_ctor_set(x_23, 0, x_66);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_63);
lean_ctor_set(x_14, 0, x_23);
x_68 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_27, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_25, x_18, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_70);
lean_dec(x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
x_75 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_14);
lean_dec(x_2);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_72, x_18, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_86;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(7, 2, 0);
} else {
 x_90 = x_82;
 lean_ctor_set_tag(x_90, 7);
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_72);
x_91 = l_Lean_MessageData_ofName(x_72);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_87);
lean_ctor_set(x_14, 0, x_92);
x_93 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_74, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_85);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_20, x_72, x_18, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_95);
lean_dec(x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_20);
lean_dec(x_18);
x_97 = lean_ctor_get(x_21, 0);
lean_inc(x_97);
lean_dec(x_21);
x_98 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_free_object(x_14);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_99);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_99, 1);
x_106 = lean_ctor_get(x_99, 0);
lean_dec(x_106);
lean_inc(x_2);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_107, 7);
lean_ctor_set(x_107, 1, x_109);
lean_ctor_set(x_107, 0, x_111);
x_112 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6;
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_112);
lean_ctor_set(x_99, 0, x_107);
lean_inc(x_97);
x_113 = l_Lean_MessageData_ofName(x_97);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_113);
lean_ctor_set(x_14, 0, x_99);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_14);
lean_ctor_set(x_114, 1, x_111);
x_115 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_98, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_110);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
x_120 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
x_122 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6;
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_122);
lean_ctor_set(x_99, 0, x_121);
lean_inc(x_97);
x_123 = l_Lean_MessageData_ofName(x_97);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_123);
lean_ctor_set(x_14, 0, x_99);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_14);
lean_ctor_set(x_124, 1, x_120);
x_125 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_98, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_119);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_128 = lean_ctor_get(x_99, 1);
lean_inc(x_128);
lean_dec(x_99);
lean_inc(x_2);
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_132;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
x_135 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_97);
x_137 = l_Lean_MessageData_ofName(x_97);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_137);
lean_ctor_set(x_14, 0, x_136);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_14);
lean_ctor_set(x_138, 1, x_133);
x_139 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_98, x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_131);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_14, 0);
x_143 = lean_ctor_get(x_14, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_2);
x_144 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___boxed), 14, 2);
lean_closure_set(x_144, 0, x_2);
lean_closure_set(x_144, 1, x_1);
x_145 = lean_ctor_get(x_142, 13);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_2, 0);
lean_inc(x_146);
x_147 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2(x_145, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_1);
lean_inc(x_2);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_2);
x_149 = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_143);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
x_154 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_153, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_151);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_152);
lean_dec(x_2);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_box(0);
x_159 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_146, x_150, x_144, x_158, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_157);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_160);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_165;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
x_168 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2;
if (lean_is_scalar(x_161)) {
 x_169 = lean_alloc_ctor(7, 2, 0);
} else {
 x_169 = x_161;
 lean_ctor_set_tag(x_169, 7);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_150);
x_170 = l_Lean_MessageData_ofName(x_150);
if (lean_is_scalar(x_152)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_152;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
x_173 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_153, x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_164);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_146, x_150, x_144, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_175);
lean_dec(x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_dec(x_146);
lean_dec(x_144);
x_177 = lean_ctor_get(x_147, 0);
lean_inc(x_177);
lean_dec(x_147);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4;
x_179 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_143);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_177, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
lean_inc(x_2);
x_186 = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(7, 2, 0);
} else {
 x_191 = x_189;
 lean_ctor_set_tag(x_191, 7);
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
x_192 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6;
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(7, 2, 0);
} else {
 x_193 = x_185;
 lean_ctor_set_tag(x_193, 7);
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_inc(x_177);
x_194 = l_Lean_MessageData_ofName(x_177);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
x_197 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_178, x_196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_188);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_2, x_1, x_177, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_198);
return x_199;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = l_Int_Linear_Poly_leadCoeff(x_14);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_17 = lean_int_dec_lt(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1;
x_20 = l_Int_Linear_Poly_mul(x_14, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_mkDiseqCnstr(x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__8(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__2(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__3(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Cutsat.processVar", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(377u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3;
x_25 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_23);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_4);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_2, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_35 = l_outOfBounds___rarg(x_31);
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq(x_27, x_3, x_35, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_PersistentArray_get_x21___rarg(x_31, x_32, x_2);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq(x_27, x_3, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_37);
return x_38;
}
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(0);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = lean_nat_dec_lt(x_2, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
x_47 = l_outOfBounds___rarg(x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7;
x_49 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__1(x_48);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(x_4, x_3, x_49, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_42);
lean_dec(x_10);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(x_4, x_3, x_51, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_42);
lean_dec(x_10);
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = l_Lean_PersistentArray_get_x21___rarg(x_43, x_44, x_2);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7;
x_55 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__1(x_54);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(x_4, x_3, x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_42);
lean_dec(x_10);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDvd(x_4, x_3, x_57, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_42);
lean_dec(x_10);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_dec(x_20);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___rarg(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Std_Internal_Rat_lt(x_5, x_6);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_6);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_findRatDiseq_x3f(x_5, x_7);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_4);
x_64 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_2, x_5, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_61);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_5);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq(x_4, x_65, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_61);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec(x_4);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_findRatVal(x_5, x_6, x_7);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_2, x_67, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_61);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_1);
x_20 = l_Std_Internal_Rat_ceil(x_1);
lean_inc(x_2);
x_21 = l_Std_Internal_Rat_floor(x_2);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_findIntVal(x_3, x_20, x_21, x_4);
lean_dec(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_5, x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1(x_22, x_5, x_6, x_7, x_1, x_2, x_4, x_37, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_resolveCooper(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_box(0);
x_33 = lean_box(x_5);
x_34 = lean_apply_12(x_3, x_32, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2___boxed), 19, 7);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_6);
lean_closure_set(x_20, 6, x_7);
lean_inc(x_2);
x_21 = l_Std_Internal_Rat_floor(x_2);
lean_inc(x_1);
x_22 = l_Std_Internal_Rat_ceil(x_1);
x_23 = lean_int_dec_lt(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_7);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict(x_7, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3(x_7, x_6, x_20, x_30, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, conflict resolution failed", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Std_Internal_Rat_lt(x_2, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict(x_7, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2;
x_28 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_26);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
return x_23;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ≤ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_getBestUpper_x3f(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(x_2, x_23, x_21);
lean_dec(x_21);
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_dec(x_33);
x_34 = l_Std_Internal_Rat_floor(x_32);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding(x_2, x_34, x_29);
lean_dec(x_29);
lean_dec(x_34);
lean_dec(x_2);
x_36 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_35);
x_37 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Std_Internal_Rat_floor(x_38);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_leAvoiding(x_2, x_39, x_29);
lean_dec(x_29);
lean_dec(x_39);
lean_dec(x_2);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_45 = x_15;
} else {
 lean_dec_ref(x_15);
 x_45 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_4);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_dec(x_50);
x_51 = l_Std_Internal_Rat_ceil(x_49);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(x_2, x_51, x_46);
lean_dec(x_46);
lean_dec(x_2);
x_53 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_44, 1, x_53);
lean_ctor_set(x_44, 0, x_52);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
x_56 = l_Std_Internal_Rat_ceil(x_55);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding(x_2, x_56, x_46);
lean_dec(x_46);
lean_dec(x_2);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_setAssignment(x_1, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_61 = lean_ctor_get(x_18, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_62 = x_18;
} else {
 lean_dec_ref(x_18);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_20, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_20, 1);
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2;
x_72 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_64);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_45);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_box(0);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5(x_65, x_68, x_2, x_63, x_1, x_69, x_66, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_dec_eq(x_84, x_85);
lean_inc(x_65);
x_87 = l_Std_Internal_Rat_ceil(x_65);
x_88 = l_Lean_quoteIfNotAtom(x_81);
lean_inc(x_68);
x_89 = l_Std_Internal_Rat_floor(x_68);
x_90 = lean_ctor_get(x_68, 1);
lean_inc(x_90);
x_91 = lean_nat_dec_eq(x_90, x_85);
if (x_86 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_65, 0);
lean_inc(x_179);
x_180 = l___private_Init_Data_Repr_0__Nat_reprFast(x_84);
x_181 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_182 = lean_int_dec_lt(x_179, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_nat_abs(x_179);
lean_dec(x_179);
x_184 = l___private_Init_Data_Repr_0__Nat_reprFast(x_183);
x_185 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_186 = lean_string_append(x_185, x_184);
lean_dec(x_184);
x_187 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_180);
lean_dec(x_180);
x_190 = lean_string_append(x_189, x_185);
x_92 = x_190;
goto block_178;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_191 = lean_nat_abs(x_179);
lean_dec(x_179);
x_192 = lean_nat_sub(x_191, x_85);
lean_dec(x_191);
x_193 = lean_nat_add(x_192, x_85);
lean_dec(x_192);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_193);
x_195 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_198 = lean_string_append(x_197, x_196);
lean_dec(x_196);
x_199 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_200 = lean_string_append(x_198, x_199);
x_201 = lean_string_append(x_200, x_180);
lean_dec(x_180);
x_202 = lean_string_append(x_201, x_197);
x_92 = x_202;
goto block_178;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_84);
x_203 = lean_ctor_get(x_65, 0);
lean_inc(x_203);
x_204 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_205 = lean_int_dec_lt(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_nat_abs(x_203);
lean_dec(x_203);
x_207 = l___private_Init_Data_Repr_0__Nat_reprFast(x_206);
x_92 = x_207;
goto block_178;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_nat_abs(x_203);
lean_dec(x_203);
x_209 = lean_nat_sub(x_208, x_85);
lean_dec(x_208);
x_210 = lean_nat_add(x_209, x_85);
lean_dec(x_209);
x_211 = l___private_Init_Data_Repr_0__Nat_reprFast(x_210);
x_212 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_213 = lean_string_append(x_212, x_211);
lean_dec(x_211);
x_92 = x_213;
goto block_178;
}
}
block_178:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_168; uint8_t x_169; 
if (lean_is_scalar(x_62)) {
 x_93 = lean_alloc_ctor(3, 1, 0);
} else {
 x_93 = x_62;
 lean_ctor_set_tag(x_93, 3);
}
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_83)) {
 x_96 = lean_alloc_ctor(7, 2, 0);
} else {
 x_96 = x_83;
 lean_ctor_set_tag(x_96, 7);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4;
if (lean_is_scalar(x_79)) {
 x_98 = lean_alloc_ctor(7, 2, 0);
} else {
 x_98 = x_79;
 lean_ctor_set_tag(x_98, 7);
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_169 = lean_int_dec_lt(x_87, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_nat_abs(x_87);
lean_dec(x_87);
x_171 = l___private_Init_Data_Repr_0__Nat_reprFast(x_170);
x_99 = x_171;
goto block_167;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_nat_abs(x_87);
lean_dec(x_87);
x_173 = lean_nat_sub(x_172, x_85);
lean_dec(x_172);
x_174 = lean_nat_add(x_173, x_85);
lean_dec(x_173);
x_175 = l___private_Init_Data_Repr_0__Nat_reprFast(x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_99 = x_177;
goto block_167;
}
block_167:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_157; uint8_t x_158; 
if (lean_is_scalar(x_45)) {
 x_100 = lean_alloc_ctor(3, 1, 0);
} else {
 x_100 = x_45;
 lean_ctor_set_tag(x_100, 3);
}
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
if (lean_is_scalar(x_70)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_70;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
if (lean_is_scalar(x_67)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_67;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_88);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_97);
x_157 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_158 = lean_int_dec_lt(x_89, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_nat_abs(x_89);
lean_dec(x_89);
x_160 = l___private_Init_Data_Repr_0__Nat_reprFast(x_159);
x_106 = x_160;
goto block_156;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_nat_abs(x_89);
lean_dec(x_89);
x_162 = lean_nat_sub(x_161, x_85);
lean_dec(x_161);
x_163 = lean_nat_add(x_162, x_85);
lean_dec(x_162);
x_164 = l___private_Init_Data_Repr_0__Nat_reprFast(x_163);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_166 = lean_string_append(x_165, x_164);
lean_dec(x_164);
x_106 = x_166;
goto block_156;
}
block_156:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_97);
if (x_91 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_68, 0);
lean_inc(x_121);
x_122 = l___private_Init_Data_Repr_0__Nat_reprFast(x_90);
x_123 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_124 = lean_int_dec_lt(x_121, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_nat_abs(x_121);
lean_dec(x_121);
x_126 = l___private_Init_Data_Repr_0__Nat_reprFast(x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_128 = lean_string_append(x_127, x_126);
lean_dec(x_126);
x_129 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_string_append(x_130, x_122);
lean_dec(x_122);
x_132 = lean_string_append(x_131, x_127);
x_111 = x_132;
goto block_120;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_133 = lean_nat_abs(x_121);
lean_dec(x_121);
x_134 = lean_nat_sub(x_133, x_85);
lean_dec(x_133);
x_135 = lean_nat_add(x_134, x_85);
lean_dec(x_134);
x_136 = l___private_Init_Data_Repr_0__Nat_reprFast(x_135);
x_137 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_138 = lean_string_append(x_137, x_136);
lean_dec(x_136);
x_139 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_140 = lean_string_append(x_139, x_138);
lean_dec(x_138);
x_141 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_string_append(x_142, x_122);
lean_dec(x_122);
x_144 = lean_string_append(x_143, x_139);
x_111 = x_144;
goto block_120;
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_90);
x_145 = lean_ctor_get(x_68, 0);
lean_inc(x_145);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_147 = lean_int_dec_lt(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_nat_abs(x_145);
lean_dec(x_145);
x_149 = l___private_Init_Data_Repr_0__Nat_reprFast(x_148);
x_111 = x_149;
goto block_120;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_nat_abs(x_145);
lean_dec(x_145);
x_151 = lean_nat_sub(x_150, x_85);
lean_dec(x_150);
x_152 = lean_nat_add(x_151, x_85);
lean_dec(x_151);
x_153 = l___private_Init_Data_Repr_0__Nat_reprFast(x_152);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_155 = lean_string_append(x_154, x_153);
lean_dec(x_153);
x_111 = x_155;
goto block_120;
}
}
block_120:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_95);
x_116 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_71, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_82);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5(x_65, x_68, x_2, x_63, x_1, x_69, x_66, x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_118);
lean_dec(x_117);
return x_119;
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
uint8_t x_214; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_20);
if (x_214 == 0)
{
return x_20;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_20, 0);
x_216 = lean_ctor_get(x_20, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_20);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_17);
if (x_218 == 0)
{
return x_17;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_17, 0);
x_220 = lean_ctor_get(x_17, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_17);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_14);
if (x_222 == 0)
{
return x_14;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_14, 0);
x_224 = lean_ctor_get(x_14, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_14);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = l_outOfBounds___rarg(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1;
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_24);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_ctor_get(x_26, 0);
lean_inc(x_40);
lean_dec(x_26);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
return x_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_25, 0);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_25);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_PersistentArray_get_x21___rarg(x_17, x_18, x_1);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1;
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_49);
x_50 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_getSolutions_x3f(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_1);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_53, 0);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_49);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_dec(x_50);
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(x_1, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_50);
if (x_67 == 0)
{
return x_50;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_50, 0);
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_50);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_processVar___spec__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__3(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_processVar(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 10);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_box(x_20);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_22, 10);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_nat_dec_eq(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_instInhabitedPUnit;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5;
x_2 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4;
x_14 = lean_panic_fn(x_13, x_1);
x_15 = lean_box(x_2);
x_16 = lean_apply_11(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_4 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skipping ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_MessageData_ofName(x_26);
x_28 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_15, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numCases > 0\n    ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1;
x_2 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Search.0.Lean.Meta.Grind.Arith.Cutsat.findCase", 91, 91);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4;
x_2 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3;
x_3 = lean_unsigned_to_nat(386u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_15 = lean_st_ref_get(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
x_22 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_3 = x_32;
x_14 = x_31;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_st_ref_get(x_5, x_17);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_19, x_42);
lean_dec(x_19);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_5, x_40);
if (x_45 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_43);
lean_dec(x_41);
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
x_131 = l_outOfBounds___rarg(x_130);
x_47 = x_131;
goto block_129;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
x_133 = l_Lean_PersistentArray_get_x21___rarg(x_132, x_41, x_43);
lean_dec(x_43);
x_47 = x_133;
goto block_129;
}
block_129:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_46, 1);
x_52 = lean_ctor_get(x_49, 0);
x_53 = l_Lean_PersistentArray_pop___rarg(x_52);
lean_ctor_set(x_49, 0, x_53);
x_54 = lean_st_ref_set(x_5, x_49, x_51);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
x_59 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_54);
lean_free_object(x_46);
x_60 = lean_box(0);
lean_inc(x_2);
x_61 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(x_2, x_47, x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_3 = x_64;
x_14 = x_63;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_dec(x_67);
lean_ctor_set(x_59, 0, x_47);
x_68 = lean_box(0);
lean_ctor_set(x_46, 1, x_68);
lean_ctor_set(x_46, 0, x_59);
lean_ctor_set(x_54, 0, x_46);
return x_54;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_47);
x_70 = lean_box(0);
lean_ctor_set(x_46, 1, x_70);
lean_ctor_set(x_46, 0, x_69);
lean_ctor_set(x_54, 0, x_46);
return x_54;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_dec(x_54);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
x_73 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_46);
x_74 = lean_box(0);
lean_inc(x_2);
x_75 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(x_2, x_47, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_71);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_3 = x_78;
x_14 = x_77;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_47);
x_82 = lean_box(0);
lean_ctor_set(x_46, 1, x_82);
lean_ctor_set(x_46, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_46);
lean_ctor_set(x_83, 1, x_71);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_46, 1);
x_85 = lean_ctor_get(x_49, 0);
x_86 = lean_ctor_get_uint8(x_49, sizeof(void*)*2);
x_87 = lean_ctor_get(x_49, 1);
lean_inc(x_87);
lean_inc(x_85);
lean_dec(x_49);
x_88 = l_Lean_PersistentArray_pop___rarg(x_85);
x_89 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_86);
x_90 = lean_st_ref_set(x_5, x_89, x_84);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
x_94 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_93);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_92);
lean_free_object(x_46);
x_95 = lean_box(0);
lean_inc(x_2);
x_96 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(x_2, x_47, x_95, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_91);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_3 = x_99;
x_14 = x_98;
goto _start;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_47);
x_103 = lean_box(0);
lean_ctor_set(x_46, 1, x_103);
lean_ctor_set(x_46, 0, x_102);
if (lean_is_scalar(x_92)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_92;
}
lean_ctor_set(x_104, 0, x_46);
lean_ctor_set(x_104, 1, x_91);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_46, 0);
x_106 = lean_ctor_get(x_46, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_46);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_105, sizeof(void*)*2);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
 x_110 = lean_box(0);
}
x_111 = l_Lean_PersistentArray_pop___rarg(x_107);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 1);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_108);
x_113 = lean_st_ref_set(x_5, x_112, x_106);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_47, 1);
lean_inc(x_116);
x_117 = l_Lean_RBNode_findCore___at_Lean_Meta_Closure_process___spec__1(x_1, x_116);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_115);
x_118 = lean_box(0);
lean_inc(x_2);
x_119 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(x_2, x_47, x_118, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_114);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_3 = x_122;
x_14 = x_121;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_47);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
if (lean_is_scalar(x_115)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_115;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_114);
return x_128;
}
}
}
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2;
x_14 = lean_panic_fn(x_13, x_1);
x_15 = lean_box(x_2);
x_16 = lean_apply_11(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4;
x_2 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3;
x_3 = lean_unsigned_to_nat(393u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1;
x_14 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___boxed), 12, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2(x_1, x_13, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1;
x_19 = lean_box(0);
x_20 = lean_box(x_2);
x_21 = lean_apply_12(x_18, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RBNode_fold___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__4(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_3 = l_Lean_RBNode_fold___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__4(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resolved diseq split: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NIY resolve conflict", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 13);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 13);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_16, 2);
lean_inc(x_28);
lean_dec(x_16);
lean_ctor_set(x_20, 1, x_28);
x_29 = lean_st_ref_set(x_6, x_19, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1;
x_34 = l_Int_Linear_Poly_mul(x_32, x_33);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_36 = l_Int_Linear_Poly_addConst(x_34, x_35);
x_37 = l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(x_27, x_1);
x_38 = l_Lean_RBTree_toArray___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__3(x_37);
x_39 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_36, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2;
x_44 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_41, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_47);
lean_dec(x_5);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_44, 1);
x_52 = lean_ctor_get(x_44, 0);
lean_dec(x_52);
lean_inc(x_41);
x_53 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_55);
lean_ctor_set(x_53, 0, x_57);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_58);
lean_ctor_set(x_44, 0, x_53);
x_59 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_43, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_41, x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_61);
lean_dec(x_5);
lean_dec(x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_53, 0);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_53);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_67);
lean_ctor_set(x_44, 0, x_66);
x_68 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_43, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_41, x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
lean_dec(x_5);
lean_dec(x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_72 = lean_ctor_get(x_44, 1);
lean_inc(x_72);
lean_dec(x_44);
lean_inc(x_41);
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(7, 2, 0);
} else {
 x_78 = x_76;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_43, x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_75);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_41, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_83);
lean_dec(x_5);
lean_dec(x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_29, 1);
lean_inc(x_85);
lean_dec(x_29);
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4;
x_87 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_85);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_20, 0);
lean_inc(x_88);
lean_dec(x_20);
x_89 = lean_ctor_get(x_16, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_16, 2);
lean_inc(x_91);
lean_dec(x_16);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_19, 13, x_92);
x_93 = lean_st_ref_set(x_6, x_19, x_21);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1;
x_98 = l_Int_Linear_Poly_mul(x_96, x_97);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_100 = l_Int_Linear_Poly_addConst(x_98, x_99);
x_101 = l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(x_90, x_1);
x_102 = l_Lean_RBTree_toArray___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__3(x_101);
x_103 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_103, 0, x_95);
lean_ctor_set(x_103, 1, x_90);
lean_ctor_set(x_103, 2, x_2);
lean_ctor_set(x_103, 3, x_102);
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_100, x_103, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_94);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2;
x_108 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_107, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_box(0);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_105, x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_111);
lean_dec(x_5);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
 x_115 = lean_box(0);
}
lean_inc(x_105);
x_116 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_105, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_114);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(7, 2, 0);
} else {
 x_121 = x_119;
 lean_ctor_set_tag(x_121, 7);
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_115)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_115;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_107, x_123, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_118);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_105, x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_126);
lean_dec(x_5);
lean_dec(x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_93, 1);
lean_inc(x_128);
lean_dec(x_93);
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4;
x_130 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(x_129, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_128);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_131 = lean_ctor_get(x_19, 0);
x_132 = lean_ctor_get(x_19, 1);
x_133 = lean_ctor_get(x_19, 2);
x_134 = lean_ctor_get(x_19, 3);
x_135 = lean_ctor_get(x_19, 4);
x_136 = lean_ctor_get(x_19, 5);
x_137 = lean_ctor_get(x_19, 6);
x_138 = lean_ctor_get_uint8(x_19, sizeof(void*)*15);
x_139 = lean_ctor_get(x_19, 7);
x_140 = lean_ctor_get(x_19, 8);
x_141 = lean_ctor_get(x_19, 9);
x_142 = lean_ctor_get(x_19, 10);
x_143 = lean_ctor_get(x_19, 11);
x_144 = lean_ctor_get(x_19, 12);
x_145 = lean_ctor_get(x_19, 14);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_19);
x_146 = lean_ctor_get(x_20, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_147 = x_20;
} else {
 lean_dec_ref(x_20);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_16, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_16, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_16, 2);
lean_inc(x_150);
lean_dec(x_16);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_152, 0, x_131);
lean_ctor_set(x_152, 1, x_132);
lean_ctor_set(x_152, 2, x_133);
lean_ctor_set(x_152, 3, x_134);
lean_ctor_set(x_152, 4, x_135);
lean_ctor_set(x_152, 5, x_136);
lean_ctor_set(x_152, 6, x_137);
lean_ctor_set(x_152, 7, x_139);
lean_ctor_set(x_152, 8, x_140);
lean_ctor_set(x_152, 9, x_141);
lean_ctor_set(x_152, 10, x_142);
lean_ctor_set(x_152, 11, x_143);
lean_ctor_set(x_152, 12, x_144);
lean_ctor_set(x_152, 13, x_151);
lean_ctor_set(x_152, 14, x_145);
lean_ctor_set_uint8(x_152, sizeof(void*)*15, x_138);
x_153 = lean_st_ref_set(x_6, x_152, x_21);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
lean_dec(x_148);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1;
x_158 = l_Int_Linear_Poly_mul(x_156, x_157);
x_159 = l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1;
x_160 = l_Int_Linear_Poly_addConst(x_158, x_159);
x_161 = l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(x_149, x_1);
x_162 = l_Lean_RBTree_toArray___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__3(x_161);
x_163 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_149);
lean_ctor_set(x_163, 2, x_2);
lean_ctor_set(x_163, 3, x_162);
x_164 = l_Lean_Meta_Grind_Arith_Cutsat_mkLeCnstr(x_160, x_163, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_154);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2;
x_168 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__5(x_167, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_box(0);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_165, x_172, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_171);
lean_dec(x_5);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_174 = lean_ctor_get(x_168, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
lean_inc(x_165);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(x_165, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_174);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2;
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(7, 2, 0);
} else {
 x_181 = x_179;
 lean_ctor_set_tag(x_181, 7);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
x_182 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_175;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10(x_167, x_183, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_178);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_165, x_185, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_186);
lean_dec(x_5);
lean_dec(x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_153, 1);
lean_inc(x_188);
lean_dec(x_153);
x_189 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4;
x_190 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(x_189, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_188);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_15);
if (x_191 == 0)
{
return x_15;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_15, 0);
x_193 = lean_ctor_get(x_15, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_15);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4;
lean_inc(x_1);
x_18 = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_collectDecVars(x_1, x_16, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_toExprProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_closeGoal(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2(x_20, x_1, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_throwError___at_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___spec__5(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 10);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_processVar(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 12);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3;
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Grind_isInconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3;
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_hasAssignment(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_2 = x_28;
x_13 = x_27;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_14, 0);
lean_dec(x_35);
x_36 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2;
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1;
x_13 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1(x_12, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_17, 3);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; double x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_27 = 0;
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_29 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_float(x_29, sizeof(void*)*2, x_26);
lean_ctor_set_float(x_29, sizeof(void*)*2 + 8, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 16, x_27);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_31 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_30);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_12);
x_32 = l_Lean_PersistentArray_push___rarg(x_25, x_16);
lean_ctor_set(x_18, 0, x_32);
x_33 = lean_st_ref_set(x_10, x_17, x_20);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint64_t x_40; lean_object* x_41; double x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get_uint64(x_18, sizeof(void*)*1);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_43 = 0;
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_45 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_float(x_45, sizeof(void*)*2, x_42);
lean_ctor_set_float(x_45, sizeof(void*)*2 + 8, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*2 + 16, x_43);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_47 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_14);
lean_ctor_set(x_47, 2, x_46);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_47);
lean_ctor_set(x_16, 0, x_12);
x_48 = l_Lean_PersistentArray_push___rarg(x_41, x_16);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_40);
lean_ctor_set(x_17, 3, x_49);
x_50 = lean_st_ref_set(x_10, x_17, x_20);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; double x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_17, 0);
x_56 = lean_ctor_get(x_17, 1);
x_57 = lean_ctor_get(x_17, 2);
x_58 = lean_ctor_get(x_17, 4);
x_59 = lean_ctor_get(x_17, 5);
x_60 = lean_ctor_get(x_17, 6);
x_61 = lean_ctor_get(x_17, 7);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_17);
x_62 = lean_ctor_get_uint64(x_18, sizeof(void*)*1);
x_63 = lean_ctor_get(x_18, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_64 = x_18;
} else {
 lean_dec_ref(x_18);
 x_64 = lean_box(0);
}
x_65 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_66 = 0;
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_68 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_float(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_float(x_68, sizeof(void*)*2 + 8, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_66);
x_69 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_70 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_12);
lean_ctor_set(x_16, 1, x_70);
lean_ctor_set(x_16, 0, x_12);
x_71 = l_Lean_PersistentArray_push___rarg(x_63, x_16);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_62);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_55);
lean_ctor_set(x_73, 1, x_56);
lean_ctor_set(x_73, 2, x_57);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_58);
lean_ctor_set(x_73, 5, x_59);
lean_ctor_set(x_73, 6, x_60);
lean_ctor_set(x_73, 7, x_61);
x_74 = lean_st_ref_set(x_10, x_73, x_20);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; double x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_79 = lean_ctor_get(x_16, 1);
lean_inc(x_79);
lean_dec(x_16);
x_80 = lean_ctor_get(x_17, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_17, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_17, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_17, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_17, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_17, 7);
lean_inc(x_86);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 x_87 = x_17;
} else {
 lean_dec_ref(x_17);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get_uint64(x_18, sizeof(void*)*1);
x_89 = lean_ctor_get(x_18, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_90 = x_18;
} else {
 lean_dec_ref(x_18);
 x_90 = lean_box(0);
}
x_91 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1;
x_92 = 0;
x_93 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_94 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_float(x_94, sizeof(void*)*2, x_91);
lean_ctor_set_float(x_94, sizeof(void*)*2 + 8, x_91);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 16, x_92);
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1;
x_96 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_14);
lean_ctor_set(x_96, 2, x_95);
lean_inc(x_12);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_PersistentArray_push___rarg(x_89, x_97);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 1, 8);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set_uint64(x_99, sizeof(void*)*1, x_88);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(0, 8, 0);
} else {
 x_100 = x_87;
}
lean_ctor_set(x_100, 0, x_80);
lean_ctor_set(x_100, 1, x_81);
lean_ctor_set(x_100, 2, x_82);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_83);
lean_ctor_set(x_100, 5, x_84);
lean_ctor_set(x_100, 6, x_85);
lean_ctor_set(x_100, 7, x_86);
x_101 = lean_st_ref_set(x_10, x_100, x_79);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_27; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_1);
x_30 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_19);
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_34;
x_21 = x_33;
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_30, 1);
x_37 = lean_ctor_get(x_30, 0);
lean_dec(x_37);
x_38 = l_Lean_quoteIfNotAtom(x_28);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_39);
x_40 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_30);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_47 = lean_int_dec_lt(x_44, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = lean_nat_abs(x_44);
lean_dec(x_44);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_45);
lean_dec(x_45);
x_55 = lean_string_append(x_54, x_50);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_MessageData_ofFormat(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_39);
lean_inc(x_1);
x_60 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_59, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_62;
x_21 = x_61;
goto block_26;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_63 = lean_nat_abs(x_44);
lean_dec(x_44);
x_64 = lean_nat_sub(x_63, x_42);
lean_dec(x_63);
x_65 = lean_nat_add(x_64, x_42);
lean_dec(x_64);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_65);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_string_append(x_72, x_45);
lean_dec(x_45);
x_74 = lean_string_append(x_73, x_69);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_19);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_39);
lean_inc(x_1);
x_79 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_78, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_81;
x_21 = x_80;
goto block_26;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_41);
x_82 = lean_ctor_get(x_29, 0);
lean_inc(x_82);
lean_dec(x_29);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_84 = lean_int_dec_lt(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_nat_abs(x_82);
lean_dec(x_82);
x_86 = l___private_Init_Data_Repr_0__Nat_reprFast(x_85);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_39);
lean_inc(x_1);
x_91 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_90, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_93;
x_21 = x_92;
goto block_26;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_nat_abs(x_82);
lean_dec(x_82);
x_95 = lean_nat_sub(x_94, x_42);
lean_dec(x_94);
x_96 = lean_nat_add(x_95, x_42);
lean_dec(x_95);
x_97 = l___private_Init_Data_Repr_0__Nat_reprFast(x_96);
x_98 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_19);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_39);
lean_inc(x_1);
x_104 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_103, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_106;
x_21 = x_105;
goto block_26;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_30, 1);
lean_inc(x_107);
lean_dec(x_30);
x_108 = l_Lean_quoteIfNotAtom(x_28);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_111);
lean_ctor_set(x_19, 0, x_110);
x_112 = lean_ctor_get(x_29, 1);
lean_inc(x_112);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_29, 0);
lean_inc(x_115);
lean_dec(x_29);
x_116 = l___private_Init_Data_Repr_0__Nat_reprFast(x_112);
x_117 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_118 = lean_int_dec_lt(x_115, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_119 = lean_nat_abs(x_115);
lean_dec(x_115);
x_120 = l___private_Init_Data_Repr_0__Nat_reprFast(x_119);
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_116);
lean_dec(x_116);
x_126 = lean_string_append(x_125, x_121);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Lean_MessageData_ofFormat(x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_19);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_109);
lean_inc(x_1);
x_131 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_130, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_107);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_133;
x_21 = x_132;
goto block_26;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_134 = lean_nat_abs(x_115);
lean_dec(x_115);
x_135 = lean_nat_sub(x_134, x_113);
lean_dec(x_134);
x_136 = lean_nat_add(x_135, x_113);
lean_dec(x_135);
x_137 = l___private_Init_Data_Repr_0__Nat_reprFast(x_136);
x_138 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_139 = lean_string_append(x_138, x_137);
lean_dec(x_137);
x_140 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_116);
lean_dec(x_116);
x_145 = lean_string_append(x_144, x_140);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_19);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_109);
lean_inc(x_1);
x_150 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_149, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_107);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_152;
x_21 = x_151;
goto block_26;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec(x_112);
x_153 = lean_ctor_get(x_29, 0);
lean_inc(x_153);
lean_dec(x_29);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_155 = lean_int_dec_lt(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = lean_nat_abs(x_153);
lean_dec(x_153);
x_157 = l___private_Init_Data_Repr_0__Nat_reprFast(x_156);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_19);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_109);
lean_inc(x_1);
x_162 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_161, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_107);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_164;
x_21 = x_163;
goto block_26;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_165 = lean_nat_abs(x_153);
lean_dec(x_153);
x_166 = lean_nat_sub(x_165, x_113);
lean_dec(x_165);
x_167 = lean_nat_add(x_166, x_113);
lean_dec(x_166);
x_168 = l___private_Init_Data_Repr_0__Nat_reprFast(x_167);
x_169 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_170 = lean_string_append(x_169, x_168);
lean_dec(x_168);
x_171 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Lean_MessageData_ofFormat(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_19);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_109);
lean_inc(x_1);
x_175 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_174, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_107);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_177;
x_21 = x_176;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_19, 0);
x_179 = lean_ctor_get(x_19, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_19);
lean_inc(x_1);
x_180 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_179);
lean_dec(x_178);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_184;
x_21 = x_183;
goto block_26;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
x_187 = l_Lean_quoteIfNotAtom(x_178);
x_188 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6;
if (lean_is_scalar(x_186)) {
 x_189 = lean_alloc_ctor(7, 2, 0);
} else {
 x_189 = x_186;
 lean_ctor_set_tag(x_189, 7);
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_ctor_get(x_179, 1);
lean_inc(x_192);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_dec_eq(x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_179, 0);
lean_inc(x_195);
lean_dec(x_179);
x_196 = l___private_Init_Data_Repr_0__Nat_reprFast(x_192);
x_197 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_198 = lean_int_dec_lt(x_195, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_199 = lean_nat_abs(x_195);
lean_dec(x_195);
x_200 = l___private_Init_Data_Repr_0__Nat_reprFast(x_199);
x_201 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_202 = lean_string_append(x_201, x_200);
lean_dec(x_200);
x_203 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_204 = lean_string_append(x_202, x_203);
x_205 = lean_string_append(x_204, x_196);
lean_dec(x_196);
x_206 = lean_string_append(x_205, x_201);
x_207 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = l_Lean_MessageData_ofFormat(x_207);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_191);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_188);
lean_inc(x_1);
x_211 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_210, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_213;
x_21 = x_212;
goto block_26;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_214 = lean_nat_abs(x_195);
lean_dec(x_195);
x_215 = lean_nat_sub(x_214, x_193);
lean_dec(x_214);
x_216 = lean_nat_add(x_215, x_193);
lean_dec(x_215);
x_217 = l___private_Init_Data_Repr_0__Nat_reprFast(x_216);
x_218 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_219 = lean_string_append(x_218, x_217);
lean_dec(x_217);
x_220 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5;
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
x_222 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_string_append(x_223, x_196);
lean_dec(x_196);
x_225 = lean_string_append(x_224, x_220);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l_Lean_MessageData_ofFormat(x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_191);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_188);
lean_inc(x_1);
x_230 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_229, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_232;
x_21 = x_231;
goto block_26;
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec(x_192);
x_233 = lean_ctor_get(x_179, 0);
lean_inc(x_233);
lean_dec(x_179);
x_234 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9;
x_235 = lean_int_dec_lt(x_233, x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_236 = lean_nat_abs(x_233);
lean_dec(x_233);
x_237 = l___private_Init_Data_Repr_0__Nat_reprFast(x_236);
x_238 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = l_Lean_MessageData_ofFormat(x_238);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_191);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_188);
lean_inc(x_1);
x_242 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_241, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_244;
x_21 = x_243;
goto block_26;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_245 = lean_nat_abs(x_233);
lean_dec(x_233);
x_246 = lean_nat_sub(x_245, x_193);
lean_dec(x_245);
x_247 = lean_nat_add(x_246, x_193);
lean_dec(x_246);
x_248 = l___private_Init_Data_Repr_0__Nat_reprFast(x_247);
x_249 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11;
x_250 = lean_string_append(x_249, x_248);
lean_dec(x_248);
x_251 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = l_Lean_MessageData_ofFormat(x_251);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_191);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_188);
lean_inc(x_1);
x_255 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_254, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_185);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1;
x_20 = x_257;
x_21 = x_256;
goto block_26;
}
}
}
}
block_26:
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
x_16 = x_21;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("model", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2;
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_st_ref_get(x_1, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(x_22, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_array_size(x_25);
x_29 = 0;
x_30 = lean_box(0);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2(x_10, x_25, x_27, x_25, x_28, x_29, x_30, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_25);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_traceModel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_traceModel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_traceModel(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_st_ref_take(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 13);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 13);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_17, 10);
lean_dec(x_24);
lean_ctor_set(x_17, 10, x_1);
x_25 = lean_st_ref_set(x_5, x_15, x_18);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_mk_ref(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_30, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_28, x_32);
lean_dec(x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_Grind_isInconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = lean_apply_10(x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_35, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
x_53 = lean_ctor_get(x_17, 2);
x_54 = lean_ctor_get(x_17, 3);
x_55 = lean_ctor_get(x_17, 4);
x_56 = lean_ctor_get(x_17, 5);
x_57 = lean_ctor_get(x_17, 6);
x_58 = lean_ctor_get(x_17, 7);
x_59 = lean_ctor_get(x_17, 8);
x_60 = lean_ctor_get(x_17, 9);
x_61 = lean_ctor_get(x_17, 11);
x_62 = lean_ctor_get_uint8(x_17, sizeof(void*)*14);
x_63 = lean_ctor_get(x_17, 12);
x_64 = lean_ctor_get(x_17, 13);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_65 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_52);
lean_ctor_set(x_65, 2, x_53);
lean_ctor_set(x_65, 3, x_54);
lean_ctor_set(x_65, 4, x_55);
lean_ctor_set(x_65, 5, x_56);
lean_ctor_set(x_65, 6, x_57);
lean_ctor_set(x_65, 7, x_58);
lean_ctor_set(x_65, 8, x_59);
lean_ctor_set(x_65, 9, x_60);
lean_ctor_set(x_65, 10, x_1);
lean_ctor_set(x_65, 11, x_61);
lean_ctor_set(x_65, 12, x_63);
lean_ctor_set(x_65, 13, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*14, x_62);
lean_ctor_set(x_16, 1, x_65);
x_66 = lean_st_ref_set(x_5, x_15, x_18);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_mk_ref(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_69);
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_71, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_get(x_69, x_73);
lean_dec(x_69);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Meta_Grind_isInconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_box(0);
x_81 = lean_apply_10(x_3, x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_69);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_86 = lean_ctor_get(x_72, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_88 = x_72;
} else {
 lean_dec_ref(x_72);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_90 = lean_ctor_get(x_16, 0);
lean_inc(x_90);
lean_dec(x_16);
x_91 = lean_ctor_get(x_17, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_17, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_17, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_17, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_17, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_17, 6);
lean_inc(x_97);
x_98 = lean_ctor_get(x_17, 7);
lean_inc(x_98);
x_99 = lean_ctor_get(x_17, 8);
lean_inc(x_99);
x_100 = lean_ctor_get(x_17, 9);
lean_inc(x_100);
x_101 = lean_ctor_get(x_17, 11);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_17, sizeof(void*)*14);
x_103 = lean_ctor_get(x_17, 12);
lean_inc(x_103);
x_104 = lean_ctor_get(x_17, 13);
lean_inc(x_104);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 lean_ctor_release(x_17, 10);
 lean_ctor_release(x_17, 11);
 lean_ctor_release(x_17, 12);
 lean_ctor_release(x_17, 13);
 x_105 = x_17;
} else {
 lean_dec_ref(x_17);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 14, 1);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_92);
lean_ctor_set(x_106, 2, x_93);
lean_ctor_set(x_106, 3, x_94);
lean_ctor_set(x_106, 4, x_95);
lean_ctor_set(x_106, 5, x_96);
lean_ctor_set(x_106, 6, x_97);
lean_ctor_set(x_106, 7, x_98);
lean_ctor_set(x_106, 8, x_99);
lean_ctor_set(x_106, 9, x_100);
lean_ctor_set(x_106, 10, x_1);
lean_ctor_set(x_106, 11, x_101);
lean_ctor_set(x_106, 12, x_103);
lean_ctor_set(x_106, 13, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*14, x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_15, 13, x_107);
x_108 = lean_st_ref_set(x_5, x_15, x_18);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_mk_ref(x_2, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_111);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_113, x_111, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_get(x_111, x_115);
lean_dec(x_111);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Meta_Grind_isInconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_box(0);
x_123 = lean_apply_10(x_3, x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_111);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_128 = lean_ctor_get(x_114, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_114, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_130 = x_114;
} else {
 lean_dec_ref(x_114);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_132 = lean_ctor_get(x_15, 0);
x_133 = lean_ctor_get(x_15, 1);
x_134 = lean_ctor_get(x_15, 2);
x_135 = lean_ctor_get(x_15, 3);
x_136 = lean_ctor_get(x_15, 4);
x_137 = lean_ctor_get(x_15, 5);
x_138 = lean_ctor_get(x_15, 6);
x_139 = lean_ctor_get_uint8(x_15, sizeof(void*)*15);
x_140 = lean_ctor_get(x_15, 7);
x_141 = lean_ctor_get(x_15, 8);
x_142 = lean_ctor_get(x_15, 9);
x_143 = lean_ctor_get(x_15, 10);
x_144 = lean_ctor_get(x_15, 11);
x_145 = lean_ctor_get(x_15, 12);
x_146 = lean_ctor_get(x_15, 14);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_15);
x_147 = lean_ctor_get(x_16, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_148 = x_16;
} else {
 lean_dec_ref(x_16);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_17, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_17, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_17, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_17, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_17, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_17, 5);
lean_inc(x_154);
x_155 = lean_ctor_get(x_17, 6);
lean_inc(x_155);
x_156 = lean_ctor_get(x_17, 7);
lean_inc(x_156);
x_157 = lean_ctor_get(x_17, 8);
lean_inc(x_157);
x_158 = lean_ctor_get(x_17, 9);
lean_inc(x_158);
x_159 = lean_ctor_get(x_17, 11);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_17, sizeof(void*)*14);
x_161 = lean_ctor_get(x_17, 12);
lean_inc(x_161);
x_162 = lean_ctor_get(x_17, 13);
lean_inc(x_162);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 lean_ctor_release(x_17, 10);
 lean_ctor_release(x_17, 11);
 lean_ctor_release(x_17, 12);
 lean_ctor_release(x_17, 13);
 x_163 = x_17;
} else {
 lean_dec_ref(x_17);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 14, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_150);
lean_ctor_set(x_164, 2, x_151);
lean_ctor_set(x_164, 3, x_152);
lean_ctor_set(x_164, 4, x_153);
lean_ctor_set(x_164, 5, x_154);
lean_ctor_set(x_164, 6, x_155);
lean_ctor_set(x_164, 7, x_156);
lean_ctor_set(x_164, 8, x_157);
lean_ctor_set(x_164, 9, x_158);
lean_ctor_set(x_164, 10, x_1);
lean_ctor_set(x_164, 11, x_159);
lean_ctor_set(x_164, 12, x_161);
lean_ctor_set(x_164, 13, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*14, x_160);
if (lean_is_scalar(x_148)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_148;
}
lean_ctor_set(x_165, 0, x_147);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_166, 0, x_132);
lean_ctor_set(x_166, 1, x_133);
lean_ctor_set(x_166, 2, x_134);
lean_ctor_set(x_166, 3, x_135);
lean_ctor_set(x_166, 4, x_136);
lean_ctor_set(x_166, 5, x_137);
lean_ctor_set(x_166, 6, x_138);
lean_ctor_set(x_166, 7, x_140);
lean_ctor_set(x_166, 8, x_141);
lean_ctor_set(x_166, 9, x_142);
lean_ctor_set(x_166, 10, x_143);
lean_ctor_set(x_166, 11, x_144);
lean_ctor_set(x_166, 12, x_145);
lean_ctor_set(x_166, 13, x_165);
lean_ctor_set(x_166, 14, x_146);
lean_ctor_set_uint8(x_166, sizeof(void*)*15, x_139);
x_167 = lean_st_ref_set(x_5, x_166, x_18);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_mk_ref(x_2, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_170);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_172, x_170, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_st_ref_get(x_170, x_174);
lean_dec(x_170);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Lean_Meta_Grind_isInconsistent(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_box(0);
x_182 = lean_apply_10(x_3, x_181, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_184 = x_177;
} else {
 lean_dec_ref(x_177);
 x_184 = lean_box(0);
}
x_185 = lean_box(0);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_187 = lean_ctor_get(x_173, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_173, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_189 = x_173;
} else {
 lean_dec_ref(x_173);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restart using Cooper resolution", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Meta_Grind_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1;
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*6 + 8);
lean_dec(x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2;
x_21 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2(x_2, x_3, x_17, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3;
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_20, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2(x_2, x_3, x_17, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_apply_10(x_17, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_apply_10(x_17, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain(x_14, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Grind_isInconsistent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3;
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3(x_18, x_24, x_10, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_18);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplit_assert___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_checkIsNextVar___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_traceAssignment___closed__11);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_skipAssignment___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars_go___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_assignElimVars___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_getBestLower_x3f___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_getDiseqValues___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveDvdConflict___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findDiseq_x3f___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdSolution_geAvoiding___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedFindIntValResult);
l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_findRatVal___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRealLowerUpperConflict___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveCooperDiseq___closed__2);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__1);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__2);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__3);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__4);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__5);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__6);
l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7 = _init_l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__1___closed__7);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__7___closed__1);
l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___spec__10___closed__1();
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__1___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___lambda__4___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveRatDiseq___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__1___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__5___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__6___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_processVar___lambda__7___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__2);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__3);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__1___closed__4);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__1);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__2);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__3);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___lambda__1___closed__4);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__1);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__2);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__3);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__2___closed__4);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___spec__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search_0__Lean_Meta_Grind_Arith_Cutsat_findCase___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___lambda__2___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_resolveConflict___closed__4);
l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3 = _init_l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_Arith_Cutsat_searchAssigmentMain___spec__1___lambda__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_Arith_Cutsat_traceModel___spec__2___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_traceModel___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___lambda__3___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_searchAssigment___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
