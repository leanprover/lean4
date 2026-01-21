// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Search
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.Proof
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4;
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_check___closed__1;
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ceil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inDiseqValues___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_check___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
uint8_t l_Rat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_toExprProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0;
lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_collectDecVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_coeff(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_leadCoeff(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1;
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Rat_floor(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_Rat_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11;
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered module", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 21);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
x_18 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 21);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
x_24 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_15 = lean_int_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_19, 30);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 23);
lean_inc_ref(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 2);
x_24 = l_Lean_mkIntLit(x_1);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_nat_dec_lt(x_2, x_23);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_21);
x_31 = l_outOfBounds___redArg(x_29);
x_25 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_PersistentArray_get_x21___redArg(x_29, x_21, x_2);
x_25 = x_32;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_mkAppB(x_22, x_24, x_25);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 30);
lean_inc_ref(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 2);
x_44 = l_Lean_instInhabitedExpr;
x_45 = lean_nat_dec_lt(x_2, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_42);
x_46 = l_outOfBounds___redArg(x_44);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_PersistentArray_get_x21___redArg(x_44, x_42, x_2);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_48, 30);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 2);
x_51 = l_Lean_instInhabitedExpr;
x_52 = lean_nat_dec_lt(x_2, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_49);
x_53 = l_outOfBounds___redArg(x_51);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_49, x_2);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_39, 0);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_19, 22);
lean_inc_ref(x_22);
lean_dec(x_19);
x_23 = l_Lean_mkAppB(x_22, x_2, x_21);
x_1 = x_17;
x_2 = x_23;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 17);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 17);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__6(x_25, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
else
{
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, structure is not an ordered int module", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 20);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
x_18 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 20);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
x_24 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 18);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = l_Lean_mkAppB(x_15, x_17, x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 18);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = l_Lean_mkAppB(x_15, x_17, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
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
lean_dec(x_15);
return x_16;
}
}
else
{
return x_14;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_36, 18);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = l_Lean_mkAppB(x_31, x_33, x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_39, 18);
lean_inc_ref(x_40);
lean_dec(x_39);
x_41 = l_Lean_mkAppB(x_31, x_33, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_33);
lean_dec(x_31);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
lean_dec(x_31);
return x_32;
}
}
else
{
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, unexpected", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1;
x_16 = l_Lean_MessageData_ofExpr(x_14);
x_17 = l_Lean_indentD(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1;
x_20 = l_Lean_Level_succ___override(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_19, x_22);
x_24 = l_Lean_mkApp3(x_23, x_17, x_1, x_2);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1;
x_29 = l_Lean_Level_succ___override(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_mkConst(x_28, x_31);
x_33 = l_Lean_mkApp3(x_32, x_26, x_1, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_15, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_mkNot(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_mkNot(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
return x_19;
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1;
x_16 = l_Lean_MessageData_ofExpr(x_14);
x_17 = l_Lean_indentD(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 18);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0(x_15, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1;
x_16 = l_Lean_MessageData_ofExpr(x_14);
x_17 = l_Lean_indentD(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal error, assigning variable out of order", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 35);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1;
x_20 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_19, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 35);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_nat_dec_eq(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1;
x_27 = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1___redArg(x_26, x_8, x_9, x_10, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_2, x_3, x_4, x_5, x_6);
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
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linarith", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("search", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assign", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5;
x_15 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_14, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; 
lean_free_object(x_15);
x_20 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; lean_object* x_39; uint8_t x_40; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_25);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_dec_eq(x_24, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_42 = lean_int_dec_lt(x_23, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_nat_abs(x_23);
lean_dec(x_23);
x_44 = l_Nat_reprFast(x_43);
x_33 = x_44;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_nat_abs(x_23);
lean_dec(x_23);
x_46 = lean_nat_sub(x_45, x_39);
lean_dec(x_45);
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_48 = lean_nat_add(x_46, x_39);
lean_dec(x_46);
x_49 = l_Nat_reprFast(x_48);
x_50 = lean_string_append(x_47, x_49);
lean_dec_ref(x_49);
x_33 = x_50;
goto block_38;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_24);
x_51 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_52 = lean_int_dec_lt(x_23, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_abs(x_23);
lean_dec(x_23);
x_54 = l_Nat_reprFast(x_53);
x_27 = x_54;
goto block_32;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_nat_abs(x_23);
lean_dec(x_23);
x_56 = lean_nat_sub(x_55, x_39);
lean_dec(x_55);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_58 = lean_nat_add(x_56, x_39);
lean_dec(x_56);
x_59 = l_Nat_reprFast(x_58);
x_60 = lean_string_append(x_57, x_59);
lean_dec_ref(x_59);
x_27 = x_60;
goto block_32;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_14, x_30, x_9, x_10, x_11, x_12);
return x_31;
}
block_38:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Nat_reprFast(x_24);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_27 = x_37;
goto block_32;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_72; lean_object* x_78; uint8_t x_79; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_21);
x_64 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_dec_eq(x_62, x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_81 = lean_int_dec_lt(x_61, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_nat_abs(x_61);
lean_dec(x_61);
x_83 = l_Nat_reprFast(x_82);
x_72 = x_83;
goto block_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_nat_abs(x_61);
lean_dec(x_61);
x_85 = lean_nat_sub(x_84, x_78);
lean_dec(x_84);
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_87 = lean_nat_add(x_85, x_78);
lean_dec(x_85);
x_88 = l_Nat_reprFast(x_87);
x_89 = lean_string_append(x_86, x_88);
lean_dec_ref(x_88);
x_72 = x_89;
goto block_77;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_62);
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_91 = lean_int_dec_lt(x_61, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_nat_abs(x_61);
lean_dec(x_61);
x_93 = l_Nat_reprFast(x_92);
x_66 = x_93;
goto block_71;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_nat_abs(x_61);
lean_dec(x_61);
x_95 = lean_nat_sub(x_94, x_78);
lean_dec(x_94);
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_97 = lean_nat_add(x_95, x_78);
lean_dec(x_95);
x_98 = l_Nat_reprFast(x_97);
x_99 = lean_string_append(x_96, x_98);
lean_dec_ref(x_98);
x_66 = x_99;
goto block_71;
}
}
block_71:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_14, x_69, x_9, x_10, x_11, x_12);
return x_70;
}
block_77:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_74 = lean_string_append(x_72, x_73);
x_75 = l_Nat_reprFast(x_62);
x_76 = lean_string_append(x_74, x_75);
lean_dec_ref(x_75);
x_66 = x_76;
goto block_71;
}
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_2);
x_100 = !lean_is_exclusive(x_20);
if (x_100 == 0)
{
return x_20;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_20, 0);
lean_inc(x_101);
lean_dec(x_20);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_15, 0);
lean_inc(x_103);
lean_dec(x_15);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_2);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_121; lean_object* x_127; uint8_t x_128; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_111 = x_2;
} else {
 lean_dec_ref(x_2);
 x_111 = lean_box(0);
}
x_112 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_108);
x_113 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7;
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(7, 2, 0);
} else {
 x_114 = x_111;
 lean_ctor_set_tag(x_114, 7);
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_dec_eq(x_110, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_130 = lean_int_dec_lt(x_109, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_nat_abs(x_109);
lean_dec(x_109);
x_132 = l_Nat_reprFast(x_131);
x_121 = x_132;
goto block_126;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_nat_abs(x_109);
lean_dec(x_109);
x_134 = lean_nat_sub(x_133, x_127);
lean_dec(x_133);
x_135 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_136 = lean_nat_add(x_134, x_127);
lean_dec(x_134);
x_137 = l_Nat_reprFast(x_136);
x_138 = lean_string_append(x_135, x_137);
lean_dec_ref(x_137);
x_121 = x_138;
goto block_126;
}
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_110);
x_139 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_140 = lean_int_dec_lt(x_109, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_nat_abs(x_109);
lean_dec(x_109);
x_142 = l_Nat_reprFast(x_141);
x_115 = x_142;
goto block_120;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_nat_abs(x_109);
lean_dec(x_109);
x_144 = lean_nat_sub(x_143, x_127);
lean_dec(x_143);
x_145 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_146 = lean_nat_add(x_144, x_127);
lean_dec(x_144);
x_147 = l_Nat_reprFast(x_146);
x_148 = lean_string_append(x_145, x_147);
lean_dec_ref(x_147);
x_115 = x_148;
goto block_120;
}
}
block_120:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lean_MessageData_ofFormat(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_14, x_118, x_9, x_10, x_11, x_12);
return x_119;
}
block_126:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_123 = lean_string_append(x_121, x_122);
x_124 = l_Nat_reprFast(x_110);
x_125 = lean_string_append(x_123, x_124);
lean_dec_ref(x_124);
x_115 = x_125;
goto block_120;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_2);
x_149 = lean_ctor_get(x_107, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_150 = x_107;
} else {
 lean_dec_ref(x_107);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 35);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = l_Lean_PersistentArray_push___redArg(x_25, x_2);
lean_ctor_set(x_23, 35, x_28);
x_29 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
x_32 = lean_ctor_get(x_23, 2);
x_33 = lean_ctor_get(x_23, 3);
x_34 = lean_ctor_get(x_23, 4);
x_35 = lean_ctor_get(x_23, 5);
x_36 = lean_ctor_get(x_23, 6);
x_37 = lean_ctor_get(x_23, 7);
x_38 = lean_ctor_get(x_23, 8);
x_39 = lean_ctor_get(x_23, 9);
x_40 = lean_ctor_get(x_23, 10);
x_41 = lean_ctor_get(x_23, 11);
x_42 = lean_ctor_get(x_23, 12);
x_43 = lean_ctor_get(x_23, 13);
x_44 = lean_ctor_get(x_23, 14);
x_45 = lean_ctor_get(x_23, 15);
x_46 = lean_ctor_get(x_23, 16);
x_47 = lean_ctor_get(x_23, 17);
x_48 = lean_ctor_get(x_23, 18);
x_49 = lean_ctor_get(x_23, 19);
x_50 = lean_ctor_get(x_23, 20);
x_51 = lean_ctor_get(x_23, 21);
x_52 = lean_ctor_get(x_23, 22);
x_53 = lean_ctor_get(x_23, 23);
x_54 = lean_ctor_get(x_23, 24);
x_55 = lean_ctor_get(x_23, 25);
x_56 = lean_ctor_get(x_23, 26);
x_57 = lean_ctor_get(x_23, 27);
x_58 = lean_ctor_get(x_23, 28);
x_59 = lean_ctor_get(x_23, 29);
x_60 = lean_ctor_get(x_23, 30);
x_61 = lean_ctor_get(x_23, 31);
x_62 = lean_ctor_get(x_23, 32);
x_63 = lean_ctor_get(x_23, 33);
x_64 = lean_ctor_get(x_23, 34);
x_65 = lean_ctor_get(x_23, 35);
x_66 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_67 = lean_ctor_get(x_23, 36);
x_68 = lean_ctor_get(x_23, 37);
x_69 = lean_ctor_get(x_23, 38);
x_70 = lean_ctor_get(x_23, 39);
x_71 = lean_ctor_get(x_23, 40);
x_72 = lean_ctor_get(x_23, 41);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
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
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
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
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_73 = lean_box(0);
x_74 = lean_array_fset(x_4, x_1, x_73);
x_75 = l_Lean_PersistentArray_push___redArg(x_65, x_2);
x_76 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_31);
lean_ctor_set(x_76, 2, x_32);
lean_ctor_set(x_76, 3, x_33);
lean_ctor_set(x_76, 4, x_34);
lean_ctor_set(x_76, 5, x_35);
lean_ctor_set(x_76, 6, x_36);
lean_ctor_set(x_76, 7, x_37);
lean_ctor_set(x_76, 8, x_38);
lean_ctor_set(x_76, 9, x_39);
lean_ctor_set(x_76, 10, x_40);
lean_ctor_set(x_76, 11, x_41);
lean_ctor_set(x_76, 12, x_42);
lean_ctor_set(x_76, 13, x_43);
lean_ctor_set(x_76, 14, x_44);
lean_ctor_set(x_76, 15, x_45);
lean_ctor_set(x_76, 16, x_46);
lean_ctor_set(x_76, 17, x_47);
lean_ctor_set(x_76, 18, x_48);
lean_ctor_set(x_76, 19, x_49);
lean_ctor_set(x_76, 20, x_50);
lean_ctor_set(x_76, 21, x_51);
lean_ctor_set(x_76, 22, x_52);
lean_ctor_set(x_76, 23, x_53);
lean_ctor_set(x_76, 24, x_54);
lean_ctor_set(x_76, 25, x_55);
lean_ctor_set(x_76, 26, x_56);
lean_ctor_set(x_76, 27, x_57);
lean_ctor_set(x_76, 28, x_58);
lean_ctor_set(x_76, 29, x_59);
lean_ctor_set(x_76, 30, x_60);
lean_ctor_set(x_76, 31, x_61);
lean_ctor_set(x_76, 32, x_62);
lean_ctor_set(x_76, 33, x_63);
lean_ctor_set(x_76, 34, x_64);
lean_ctor_set(x_76, 35, x_75);
lean_ctor_set(x_76, 36, x_67);
lean_ctor_set(x_76, 37, x_68);
lean_ctor_set(x_76, 38, x_69);
lean_ctor_set(x_76, 39, x_70);
lean_ctor_set(x_76, 40, x_71);
lean_ctor_set(x_76, 41, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*42, x_66);
x_77 = lean_array_fset(x_74, x_1, x_76);
lean_ctor_set(x_3, 0, x_77);
return x_3;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
x_78 = lean_array_fget(x_4, x_1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 11);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 12);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 13);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 14);
lean_inc(x_93);
x_94 = lean_ctor_get(x_78, 15);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 16);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 17);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_78, 18);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_78, 19);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 20);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 21);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 22);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_78, 23);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_78, 24);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_78, 25);
lean_inc(x_104);
x_105 = lean_ctor_get(x_78, 26);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 27);
lean_inc(x_106);
x_107 = lean_ctor_get(x_78, 28);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_78, 29);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_78, 30);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_78, 31);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_78, 32);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_78, 33);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_78, 34);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_78, 35);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_78, sizeof(void*)*42);
x_116 = lean_ctor_get(x_78, 36);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 37);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_78, 38);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_78, 39);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 40);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_78, 41);
lean_inc_ref(x_121);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 lean_ctor_release(x_78, 9);
 lean_ctor_release(x_78, 10);
 lean_ctor_release(x_78, 11);
 lean_ctor_release(x_78, 12);
 lean_ctor_release(x_78, 13);
 lean_ctor_release(x_78, 14);
 lean_ctor_release(x_78, 15);
 lean_ctor_release(x_78, 16);
 lean_ctor_release(x_78, 17);
 lean_ctor_release(x_78, 18);
 lean_ctor_release(x_78, 19);
 lean_ctor_release(x_78, 20);
 lean_ctor_release(x_78, 21);
 lean_ctor_release(x_78, 22);
 lean_ctor_release(x_78, 23);
 lean_ctor_release(x_78, 24);
 lean_ctor_release(x_78, 25);
 lean_ctor_release(x_78, 26);
 lean_ctor_release(x_78, 27);
 lean_ctor_release(x_78, 28);
 lean_ctor_release(x_78, 29);
 lean_ctor_release(x_78, 30);
 lean_ctor_release(x_78, 31);
 lean_ctor_release(x_78, 32);
 lean_ctor_release(x_78, 33);
 lean_ctor_release(x_78, 34);
 lean_ctor_release(x_78, 35);
 lean_ctor_release(x_78, 36);
 lean_ctor_release(x_78, 37);
 lean_ctor_release(x_78, 38);
 lean_ctor_release(x_78, 39);
 lean_ctor_release(x_78, 40);
 lean_ctor_release(x_78, 41);
 x_122 = x_78;
} else {
 lean_dec_ref(x_78);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
x_124 = lean_array_fset(x_4, x_1, x_123);
x_125 = l_Lean_PersistentArray_push___redArg(x_114, x_2);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 42, 1);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_79);
lean_ctor_set(x_126, 1, x_80);
lean_ctor_set(x_126, 2, x_81);
lean_ctor_set(x_126, 3, x_82);
lean_ctor_set(x_126, 4, x_83);
lean_ctor_set(x_126, 5, x_84);
lean_ctor_set(x_126, 6, x_85);
lean_ctor_set(x_126, 7, x_86);
lean_ctor_set(x_126, 8, x_87);
lean_ctor_set(x_126, 9, x_88);
lean_ctor_set(x_126, 10, x_89);
lean_ctor_set(x_126, 11, x_90);
lean_ctor_set(x_126, 12, x_91);
lean_ctor_set(x_126, 13, x_92);
lean_ctor_set(x_126, 14, x_93);
lean_ctor_set(x_126, 15, x_94);
lean_ctor_set(x_126, 16, x_95);
lean_ctor_set(x_126, 17, x_96);
lean_ctor_set(x_126, 18, x_97);
lean_ctor_set(x_126, 19, x_98);
lean_ctor_set(x_126, 20, x_99);
lean_ctor_set(x_126, 21, x_100);
lean_ctor_set(x_126, 22, x_101);
lean_ctor_set(x_126, 23, x_102);
lean_ctor_set(x_126, 24, x_103);
lean_ctor_set(x_126, 25, x_104);
lean_ctor_set(x_126, 26, x_105);
lean_ctor_set(x_126, 27, x_106);
lean_ctor_set(x_126, 28, x_107);
lean_ctor_set(x_126, 29, x_108);
lean_ctor_set(x_126, 30, x_109);
lean_ctor_set(x_126, 31, x_110);
lean_ctor_set(x_126, 32, x_111);
lean_ctor_set(x_126, 33, x_112);
lean_ctor_set(x_126, 34, x_113);
lean_ctor_set(x_126, 35, x_125);
lean_ctor_set(x_126, 36, x_116);
lean_ctor_set(x_126, 37, x_117);
lean_ctor_set(x_126, 38, x_118);
lean_ctor_set(x_126, 39, x_119);
lean_ctor_set(x_126, 40, x_120);
lean_ctor_set(x_126, 41, x_121);
lean_ctor_set_uint8(x_126, sizeof(void*)*42, x_115);
x_127 = lean_array_fset(x_124, x_1, x_126);
x_128 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_5);
lean_ctor_set(x_128, 2, x_6);
lean_ctor_set(x_128, 3, x_7);
lean_ctor_set(x_128, 4, x_8);
lean_ctor_set(x_128, 5, x_9);
lean_ctor_set(x_128, 6, x_10);
lean_ctor_set(x_128, 7, x_11);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_14);
lean_inc_ref(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_15);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___lam__0___boxed), 3, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_2);
x_17 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_18 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_17, x_16, x_4);
return x_18;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Rat_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_neg(x_37);
x_39 = l_Rat_div(x_35, x_38);
lean_dec(x_35);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_39);
lean_inc(x_46);
x_48 = l_Rat_blt(x_46, x_39);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_neg(x_37);
x_39 = l_Rat_div(x_35, x_38);
lean_dec(x_35);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_39);
lean_inc(x_46);
x_48 = l_Rat_blt(x_46, x_39);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2_spec__5(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_neg(x_37);
x_39 = l_Rat_div(x_35, x_38);
lean_dec(x_35);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_39);
lean_inc(x_46);
x_48 = l_Rat_blt(x_46, x_39);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_neg(x_37);
x_39 = l_Rat_div(x_35, x_38);
lean_dec(x_35);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_39);
lean_inc(x_46);
x_48 = l_Rat_blt(x_46, x_39);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3_spec__4(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(x_1, x_17, x_16, x_19, x_20, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_24);
lean_dec(x_23);
lean_free_object(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_28);
lean_dec(x_27);
lean_free_object(x_2);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(x_1, x_37, x_36, x_39, x_40, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
x_57 = lean_array_size(x_54);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(x_55, x_54, x_57, x_58, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_ctor_set(x_2, 0, x_63);
lean_ctor_set(x_59, 0, x_2);
return x_59;
}
else
{
lean_object* x_64; 
lean_inc_ref(x_62);
lean_dec(x_61);
lean_free_object(x_2);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_65, 0);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_ctor_set(x_2, 0, x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_inc_ref(x_66);
lean_dec(x_65);
lean_free_object(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_2);
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
lean_dec(x_59);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
x_77 = lean_array_size(x_74);
x_78 = 0;
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__3(x_75, x_74, x_77, x_78, x_76, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_82);
lean_dec(x_80);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec_ref(x_82);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_3, x_5);
lean_inc(x_21);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_1, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_24);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_2);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_6);
return x_34;
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_21);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_21);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_array_uget(x_3, x_5);
lean_inc(x_42);
x_44 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_1, x_43, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_46);
lean_dec(x_42);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec_ref(x_45);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_42);
lean_dec(x_2);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
lean_inc(x_2);
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__1(x_2, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_16);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_15);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(x_21, x_15, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; 
lean_inc_ref(x_28);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_size(x_15);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1_spec__2(x_44, x_15, x_46, x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_49, 0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_51);
lean_dec(x_49);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_15);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 32);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 2);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0;
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_1, x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = l_outOfBounds___redArg(x_17);
x_21 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_20, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_PersistentArray_get_x21___redArg(x_17, x_15, x_1);
x_23 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestLower_x3f_spec__1(x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_neg(x_35);
x_38 = l_Rat_ofInt(x_31);
x_39 = l_Rat_div(x_37, x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_inc_ref(x_39);
x_48 = l_Rat_blt(x_39, x_46);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_neg(x_35);
x_38 = l_Rat_ofInt(x_31);
x_39 = l_Rat_div(x_37, x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_inc_ref(x_39);
x_48 = l_Rat_blt(x_39, x_46);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(x_1, x_17, x_16, x_19, x_20, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_24);
lean_dec(x_23);
lean_free_object(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_28);
lean_dec(x_27);
lean_free_object(x_2);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(x_1, x_37, x_36, x_39, x_40, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
x_57 = lean_array_size(x_54);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(x_55, x_54, x_57, x_58, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_ctor_set(x_2, 0, x_63);
lean_ctor_set(x_59, 0, x_2);
return x_59;
}
else
{
lean_object* x_64; 
lean_inc_ref(x_62);
lean_dec(x_61);
lean_free_object(x_2);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_65, 0);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_ctor_set(x_2, 0, x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_inc_ref(x_66);
lean_dec(x_65);
lean_free_object(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_2);
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
lean_dec(x_59);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
x_77 = lean_array_size(x_74);
x_78 = 0;
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__2(x_75, x_74, x_77, x_78, x_76, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_82);
lean_dec(x_80);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec_ref(x_82);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_3, x_5);
lean_inc(x_21);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_1, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_24);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_2);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_6);
return x_34;
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_21);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_21);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_array_uget(x_3, x_5);
lean_inc(x_42);
x_44 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_1, x_43, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_46);
lean_dec(x_42);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec_ref(x_45);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_42);
lean_dec(x_2);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_neg(x_35);
x_38 = l_Rat_ofInt(x_31);
x_39 = l_Rat_div(x_37, x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_inc_ref(x_39);
x_48 = l_Rat_blt(x_39, x_46);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_27 = x_5;
} else {
 lean_dec_ref(x_5);
 x_27 = lean_box(0);
}
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Rat_neg(x_35);
x_38 = l_Rat_ofInt(x_31);
x_39 = l_Rat_div(x_37, x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_inc_ref(x_39);
x_48 = l_Rat_blt(x_39, x_46);
if (x_48 == 0)
{
uint8_t x_52; 
x_52 = l_instDecidableEqRat_decEq(x_39, x_46);
if (x_52 == 0)
{
x_49 = x_52;
goto block_51;
}
else
{
x_49 = x_30;
goto block_51;
}
}
else
{
x_43 = x_48;
goto block_44;
}
block_51:
{
if (x_49 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
if (x_50 == 0)
{
lean_dec_ref(x_26);
goto block_42;
}
else
{
x_43 = x_48;
goto block_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_28);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = lean_box(0);
goto block_23;
}
block_44:
{
if (x_43 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_27);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_dec(x_26);
goto block_42;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_27);
x_55 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
return x_33;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_29);
lean_dec(x_27);
x_62 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_62);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_63; 
lean_dec(x_26);
lean_dec(x_1);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
lean_inc(x_2);
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__0(x_2, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_16);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_15);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(x_21, x_15, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; 
lean_inc_ref(x_28);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_size(x_15);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0_spec__1(x_44, x_15, x_46, x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_49, 0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_51);
lean_dec(x_49);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_15);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 33);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 2);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0;
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_1, x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = l_outOfBounds___redArg(x_17);
x_21 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_20, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_PersistentArray_get_x21___redArg(x_17, x_15, x_1);
x_23 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f_spec__0(x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_array_uget(x_2, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Rat_neg(x_35);
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_div(x_36, x_37);
lean_dec_ref(x_36);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_38);
x_39 = lean_array_push(x_27, x_5);
x_17 = x_39;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_5);
x_40 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_29);
lean_free_object(x_5);
lean_dec(x_27);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_30);
lean_free_object(x_5);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_array_uget(x_2, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Rat_neg(x_58);
x_60 = l_Rat_ofInt(x_54);
x_61 = l_Rat_div(x_59, x_60);
lean_dec_ref(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_push(x_51, x_62);
x_17 = x_63;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_54);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_53);
x_71 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_array_uget(x_2, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Rat_neg(x_35);
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_div(x_36, x_37);
lean_dec_ref(x_36);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_38);
x_39 = lean_array_push(x_27, x_5);
x_17 = x_39;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_5);
x_40 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_29);
lean_free_object(x_5);
lean_dec(x_27);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_30);
lean_free_object(x_5);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_array_uget(x_2, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Rat_neg(x_58);
x_60 = l_Rat_ofInt(x_54);
x_61 = l_Rat_div(x_59, x_60);
lean_dec_ref(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_push(x_51, x_62);
x_17 = x_63;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_54);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_53);
x_71 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_array_uget(x_2, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Rat_neg(x_35);
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_div(x_36, x_37);
lean_dec_ref(x_36);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_38);
x_39 = lean_array_push(x_27, x_5);
x_17 = x_39;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_5);
x_40 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_29);
lean_free_object(x_5);
lean_dec(x_27);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_30);
lean_free_object(x_5);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_array_uget(x_2, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Rat_neg(x_58);
x_60 = l_Rat_ofInt(x_54);
x_61 = l_Rat_div(x_59, x_60);
lean_dec_ref(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_push(x_51, x_62);
x_17 = x_63;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_54);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_53);
x_71 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_4, x_3);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_array_uget(x_2, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Rat_neg(x_35);
x_37 = l_Rat_ofInt(x_31);
x_38 = l_Rat_div(x_36, x_37);
lean_dec_ref(x_36);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_38);
x_39 = lean_array_push(x_27, x_5);
x_17 = x_39;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_31);
lean_free_object(x_5);
x_40 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_29);
lean_free_object(x_5);
lean_dec(x_27);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_30);
lean_free_object(x_5);
x_47 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_17 = x_27;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_array_uget(x_2, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Rat_neg(x_58);
x_60 = l_Rat_ofInt(x_54);
x_61 = l_Rat_div(x_59, x_60);
lean_dec_ref(x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_array_push(x_51, x_62);
x_17 = x_63;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_54);
x_64 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_53);
x_71 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected___redArg(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_52);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_17 = x_51;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(x_1, x_17, x_16, x_19, x_20, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_24);
lean_dec(x_23);
lean_free_object(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_28);
lean_dec(x_27);
lean_free_object(x_2);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_array_size(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(x_1, x_37, x_36, x_39, x_40, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
x_57 = lean_array_size(x_54);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(x_55, x_54, x_57, x_58, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_ctor_set(x_2, 0, x_63);
lean_ctor_set(x_59, 0, x_2);
return x_59;
}
else
{
lean_object* x_64; 
lean_inc_ref(x_62);
lean_dec(x_61);
lean_free_object(x_2);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_65, 0);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_ctor_set(x_2, 0, x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_inc_ref(x_66);
lean_dec(x_65);
lean_free_object(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_2);
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
lean_dec(x_59);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_3);
x_77 = lean_array_size(x_74);
x_78 = 0;
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__2(x_75, x_74, x_77, x_78, x_76, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_82);
lean_dec(x_80);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec_ref(x_82);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_3, x_5);
lean_inc(x_21);
x_24 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_1, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_24);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_2);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_6);
return x_34;
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_21);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_2);
x_36 = 1;
x_37 = lean_usize_add(x_5, x_36);
x_5 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_21);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_dec(x_6);
x_43 = lean_array_uget(x_3, x_5);
lean_inc(x_42);
x_44 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_1, x_43, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_46);
lean_dec(x_42);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec_ref(x_45);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_42);
lean_dec(x_2);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_16 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__0(x_2, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_16);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_15);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(x_21, x_15, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; 
lean_inc_ref(x_28);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_size(x_15);
x_47 = 0;
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0_spec__1(x_44, x_15, x_46, x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_49, 0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_51);
lean_dec(x_49);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_15);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 34);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 2);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0;
x_18 = l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0;
x_19 = lean_nat_dec_lt(x_1, x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = l_outOfBounds___redArg(x_17);
x_21 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_20, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_PersistentArray_get_x21___redArg(x_17, x_15, x_1);
x_23 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_getDiseqValues_spec__0(x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_instDecidableEqRat_decEq(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
size_t x_12; size_t x_13; 
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
{
size_t _tmp_5 = x_13;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0;
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_findDiseq_x3f_spec__0(x_1, x_5, x_4, x_2, x_6, x_7, x_5);
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
if (lean_obj_tag(x_10) == 0)
{
return x_3;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inDiseqValues___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
x_5 = l_Rat_add(x_1, x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_geAvoiding___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
x_5 = l_Rat_sub(x_1, x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_leAvoiding___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_leAvoiding(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("conflict", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1;
x_61 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg(x_60, x_11);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_MessageData_ofExpr(x_65);
x_69 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_MessageData_ofExpr(x_67);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg(x_60, x_72, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = lean_box(0);
goto block_59;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_65);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
return x_66;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
lean_dec(x_66);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
return x_64;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
x_29 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_28, x_21, x_19, x_22, x_16, x_24, x_17, x_25, x_15, x_18, x_23);
return x_29;
}
block_59:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_43) == 1)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 2);
x_50 = lean_nat_abs(x_48);
x_51 = lean_nat_to_int(x_50);
lean_inc(x_46);
x_52 = l_Lean_Grind_Linarith_Poly_mul(x_46, x_51);
lean_dec(x_51);
x_53 = lean_nat_abs(x_45);
x_54 = lean_nat_to_int(x_53);
lean_inc(x_49);
x_55 = l_Lean_Grind_Linarith_Poly_mul(x_49, x_54);
lean_dec(x_54);
x_56 = l_Lean_Grind_Linarith_Poly_combine(x_52, x_55);
if (x_44 == 0)
{
x_14 = lean_box(0);
x_15 = x_38;
x_16 = x_34;
x_17 = x_36;
x_18 = x_39;
x_19 = x_32;
x_20 = x_56;
x_21 = x_31;
x_22 = x_33;
x_23 = x_40;
x_24 = x_35;
x_25 = x_37;
x_26 = x_47;
goto block_30;
}
else
{
x_14 = lean_box(0);
x_15 = x_38;
x_16 = x_34;
x_17 = x_36;
x_18 = x_39;
x_19 = x_32;
x_20 = x_56;
x_21 = x_31;
x_22 = x_33;
x_23 = x_40;
x_24 = x_35;
x_25 = x_37;
x_26 = x_44;
goto block_30;
}
}
else
{
lean_object* x_57; 
lean_dec_ref(x_1);
x_57 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_2, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_2);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_2);
x_58 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg(x_1, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_int_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Rat_ofInt(x_2);
x_6 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_8 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_9 = lean_int_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_14; lean_object* x_19; uint8_t x_20; lean_object* x_24; uint8_t x_25; 
lean_inc_ref(x_1);
x_19 = l_Rat_ceil(x_1);
lean_inc(x_19);
x_24 = l_Rat_ofInt(x_19);
x_25 = l_instDecidableEqRat_decEq(x_24, x_1);
lean_dec_ref(x_1);
lean_dec_ref(x_24);
if (x_25 == 0)
{
x_20 = x_25;
goto block_23;
}
else
{
x_20 = x_2;
goto block_23;
}
block_13:
{
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_5, x_7, x_6);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_11 = lean_int_sub(x_6, x_10);
lean_dec(x_6);
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findInt_x3f_go(x_5, x_7, x_11);
lean_dec(x_11);
return x_12;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc_ref(x_3);
x_15 = l_Rat_floor(x_3);
lean_inc(x_15);
x_16 = l_Rat_ofInt(x_15);
x_17 = l_instDecidableEqRat_decEq(x_16, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_16);
if (x_17 == 0)
{
x_6 = x_15;
x_7 = x_14;
x_8 = x_17;
goto block_13;
}
else
{
x_6 = x_15;
x_7 = x_14;
x_8 = x_4;
goto block_13;
}
}
block_23:
{
if (x_20 == 0)
{
x_14 = x_19;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_19);
x_14 = x_22;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_4);
x_8 = l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(x_1, x_6, x_3, x_7, x_5);
lean_dec_ref(x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc_ref(x_2);
x_4 = l_Rat_add(x_1, x_2);
x_5 = l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0;
x_6 = l_Rat_div(x_4, x_5);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Grind_Arith_Linear_inDiseqValues(x_6, x_3);
if (x_7 == 0)
{
lean_dec_ref(x_2);
return x_6;
}
else
{
x_1 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_findRat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_findRat(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 37);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_26, x_2, x_3);
lean_ctor_set(x_24, 37, x_29);
x_30 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_ctor_get(x_24, 2);
x_34 = lean_ctor_get(x_24, 3);
x_35 = lean_ctor_get(x_24, 4);
x_36 = lean_ctor_get(x_24, 5);
x_37 = lean_ctor_get(x_24, 6);
x_38 = lean_ctor_get(x_24, 7);
x_39 = lean_ctor_get(x_24, 8);
x_40 = lean_ctor_get(x_24, 9);
x_41 = lean_ctor_get(x_24, 10);
x_42 = lean_ctor_get(x_24, 11);
x_43 = lean_ctor_get(x_24, 12);
x_44 = lean_ctor_get(x_24, 13);
x_45 = lean_ctor_get(x_24, 14);
x_46 = lean_ctor_get(x_24, 15);
x_47 = lean_ctor_get(x_24, 16);
x_48 = lean_ctor_get(x_24, 17);
x_49 = lean_ctor_get(x_24, 18);
x_50 = lean_ctor_get(x_24, 19);
x_51 = lean_ctor_get(x_24, 20);
x_52 = lean_ctor_get(x_24, 21);
x_53 = lean_ctor_get(x_24, 22);
x_54 = lean_ctor_get(x_24, 23);
x_55 = lean_ctor_get(x_24, 24);
x_56 = lean_ctor_get(x_24, 25);
x_57 = lean_ctor_get(x_24, 26);
x_58 = lean_ctor_get(x_24, 27);
x_59 = lean_ctor_get(x_24, 28);
x_60 = lean_ctor_get(x_24, 29);
x_61 = lean_ctor_get(x_24, 30);
x_62 = lean_ctor_get(x_24, 31);
x_63 = lean_ctor_get(x_24, 32);
x_64 = lean_ctor_get(x_24, 33);
x_65 = lean_ctor_get(x_24, 34);
x_66 = lean_ctor_get(x_24, 35);
x_67 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_68 = lean_ctor_get(x_24, 36);
x_69 = lean_ctor_get(x_24, 37);
x_70 = lean_ctor_get(x_24, 38);
x_71 = lean_ctor_get(x_24, 39);
x_72 = lean_ctor_get(x_24, 40);
x_73 = lean_ctor_get(x_24, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
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
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
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
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_5, x_1, x_74);
x_76 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_69, x_2, x_3);
x_77 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_32);
lean_ctor_set(x_77, 2, x_33);
lean_ctor_set(x_77, 3, x_34);
lean_ctor_set(x_77, 4, x_35);
lean_ctor_set(x_77, 5, x_36);
lean_ctor_set(x_77, 6, x_37);
lean_ctor_set(x_77, 7, x_38);
lean_ctor_set(x_77, 8, x_39);
lean_ctor_set(x_77, 9, x_40);
lean_ctor_set(x_77, 10, x_41);
lean_ctor_set(x_77, 11, x_42);
lean_ctor_set(x_77, 12, x_43);
lean_ctor_set(x_77, 13, x_44);
lean_ctor_set(x_77, 14, x_45);
lean_ctor_set(x_77, 15, x_46);
lean_ctor_set(x_77, 16, x_47);
lean_ctor_set(x_77, 17, x_48);
lean_ctor_set(x_77, 18, x_49);
lean_ctor_set(x_77, 19, x_50);
lean_ctor_set(x_77, 20, x_51);
lean_ctor_set(x_77, 21, x_52);
lean_ctor_set(x_77, 22, x_53);
lean_ctor_set(x_77, 23, x_54);
lean_ctor_set(x_77, 24, x_55);
lean_ctor_set(x_77, 25, x_56);
lean_ctor_set(x_77, 26, x_57);
lean_ctor_set(x_77, 27, x_58);
lean_ctor_set(x_77, 28, x_59);
lean_ctor_set(x_77, 29, x_60);
lean_ctor_set(x_77, 30, x_61);
lean_ctor_set(x_77, 31, x_62);
lean_ctor_set(x_77, 32, x_63);
lean_ctor_set(x_77, 33, x_64);
lean_ctor_set(x_77, 34, x_65);
lean_ctor_set(x_77, 35, x_66);
lean_ctor_set(x_77, 36, x_68);
lean_ctor_set(x_77, 37, x_76);
lean_ctor_set(x_77, 38, x_70);
lean_ctor_set(x_77, 39, x_71);
lean_ctor_set(x_77, 40, x_72);
lean_ctor_set(x_77, 41, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*42, x_67);
x_78 = lean_array_fset(x_75, x_1, x_77);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_79 = lean_array_fget(x_5, x_1);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 14);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 15);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 16);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 17);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 18);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 19);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 20);
lean_inc(x_100);
x_101 = lean_ctor_get(x_79, 21);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 22);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_79, 23);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_79, 24);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_79, 25);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 26);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 27);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 28);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_79, 29);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_79, 30);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_79, 31);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_79, 32);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_79, 33);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_79, 34);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_79, 35);
lean_inc_ref(x_115);
x_116 = lean_ctor_get_uint8(x_79, sizeof(void*)*42);
x_117 = lean_ctor_get(x_79, 36);
lean_inc(x_117);
x_118 = lean_ctor_get(x_79, 37);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_79, 38);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_79, 39);
lean_inc(x_120);
x_121 = lean_ctor_get(x_79, 40);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_79, 41);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 lean_ctor_release(x_79, 9);
 lean_ctor_release(x_79, 10);
 lean_ctor_release(x_79, 11);
 lean_ctor_release(x_79, 12);
 lean_ctor_release(x_79, 13);
 lean_ctor_release(x_79, 14);
 lean_ctor_release(x_79, 15);
 lean_ctor_release(x_79, 16);
 lean_ctor_release(x_79, 17);
 lean_ctor_release(x_79, 18);
 lean_ctor_release(x_79, 19);
 lean_ctor_release(x_79, 20);
 lean_ctor_release(x_79, 21);
 lean_ctor_release(x_79, 22);
 lean_ctor_release(x_79, 23);
 lean_ctor_release(x_79, 24);
 lean_ctor_release(x_79, 25);
 lean_ctor_release(x_79, 26);
 lean_ctor_release(x_79, 27);
 lean_ctor_release(x_79, 28);
 lean_ctor_release(x_79, 29);
 lean_ctor_release(x_79, 30);
 lean_ctor_release(x_79, 31);
 lean_ctor_release(x_79, 32);
 lean_ctor_release(x_79, 33);
 lean_ctor_release(x_79, 34);
 lean_ctor_release(x_79, 35);
 lean_ctor_release(x_79, 36);
 lean_ctor_release(x_79, 37);
 lean_ctor_release(x_79, 38);
 lean_ctor_release(x_79, 39);
 lean_ctor_release(x_79, 40);
 lean_ctor_release(x_79, 41);
 x_123 = x_79;
} else {
 lean_dec_ref(x_79);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_array_fset(x_5, x_1, x_124);
x_126 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_118, x_2, x_3);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 42, 1);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_80);
lean_ctor_set(x_127, 1, x_81);
lean_ctor_set(x_127, 2, x_82);
lean_ctor_set(x_127, 3, x_83);
lean_ctor_set(x_127, 4, x_84);
lean_ctor_set(x_127, 5, x_85);
lean_ctor_set(x_127, 6, x_86);
lean_ctor_set(x_127, 7, x_87);
lean_ctor_set(x_127, 8, x_88);
lean_ctor_set(x_127, 9, x_89);
lean_ctor_set(x_127, 10, x_90);
lean_ctor_set(x_127, 11, x_91);
lean_ctor_set(x_127, 12, x_92);
lean_ctor_set(x_127, 13, x_93);
lean_ctor_set(x_127, 14, x_94);
lean_ctor_set(x_127, 15, x_95);
lean_ctor_set(x_127, 16, x_96);
lean_ctor_set(x_127, 17, x_97);
lean_ctor_set(x_127, 18, x_98);
lean_ctor_set(x_127, 19, x_99);
lean_ctor_set(x_127, 20, x_100);
lean_ctor_set(x_127, 21, x_101);
lean_ctor_set(x_127, 22, x_102);
lean_ctor_set(x_127, 23, x_103);
lean_ctor_set(x_127, 24, x_104);
lean_ctor_set(x_127, 25, x_105);
lean_ctor_set(x_127, 26, x_106);
lean_ctor_set(x_127, 27, x_107);
lean_ctor_set(x_127, 28, x_108);
lean_ctor_set(x_127, 29, x_109);
lean_ctor_set(x_127, 30, x_110);
lean_ctor_set(x_127, 31, x_111);
lean_ctor_set(x_127, 32, x_112);
lean_ctor_set(x_127, 33, x_113);
lean_ctor_set(x_127, 34, x_114);
lean_ctor_set(x_127, 35, x_115);
lean_ctor_set(x_127, 36, x_117);
lean_ctor_set(x_127, 37, x_126);
lean_ctor_set(x_127, 38, x_119);
lean_ctor_set(x_127, 39, x_120);
lean_ctor_set(x_127, 40, x_121);
lean_ctor_set(x_127, 41, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*42, x_116);
x_128 = lean_array_fset(x_125, x_1, x_127);
x_129 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_6);
lean_ctor_set(x_129, 2, x_7);
lean_ctor_set(x_129, 3, x_8);
lean_ctor_set(x_129, 4, x_9);
lean_ctor_set(x_129, 5, x_10);
lean_ctor_set(x_129, 6, x_11);
lean_ctor_set(x_129, 7, x_12);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_2, x_3, x_4, x_5, x_6);
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
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_12);
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
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
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
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_Grind_Linarith_instBEqPoly_beq(x_3, x_27);
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
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
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
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1;
x_20 = l_Lean_Level_succ___override(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkConst(x_19, x_22);
x_24 = l_Lean_mkApp3(x_23, x_17, x_1, x_2);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1;
x_29 = l_Lean_Level_succ___override(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_mkConst(x_28, x_31);
x_33 = l_Lean_mkApp3(x_32, x_26, x_1, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_15 = lean_int_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_19, 30);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 23);
lean_inc_ref(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 2);
x_24 = l_Lean_mkIntLit(x_1);
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_nat_dec_lt(x_2, x_23);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_21);
x_31 = l_outOfBounds___redArg(x_29);
x_25 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_PersistentArray_get_x21___redArg(x_29, x_21, x_2);
x_25 = x_32;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_mkAppB(x_22, x_24, x_25);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 30);
lean_inc_ref(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 2);
x_44 = l_Lean_instInhabitedExpr;
x_45 = lean_nat_dec_lt(x_2, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_42);
x_46 = l_outOfBounds___redArg(x_44);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_PersistentArray_get_x21___redArg(x_44, x_42, x_2);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_48, 30);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 2);
x_51 = l_Lean_instInhabitedExpr;
x_52 = lean_nat_dec_lt(x_2, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_49);
x_53 = l_outOfBounds___redArg(x_51);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_49, x_2);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_39, 0);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_20, 22);
lean_inc_ref(x_23);
lean_dec(x_20);
x_24 = l_Lean_mkAppB(x_23, x_2, x_22);
x_1 = x_18;
x_2 = x_24;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 17);
lean_inc_ref(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 17);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_24, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__6(x_26, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
else
{
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 18);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_16, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkNot(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_mkNot(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
return x_20;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", reusing ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_15, 37);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_26 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_17, x_18);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1;
x_29 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_28, x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
x_19 = x_27;
x_20 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec_ref(x_32);
x_37 = l_Lean_MessageData_ofExpr(x_36);
x_38 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
lean_inc(x_27);
x_39 = l_Lean_MessageData_ofName(x_27);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_28, x_40, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_19 = x_27;
x_20 = lean_box(0);
goto block_25;
}
else
{
uint8_t x_42; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_16);
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
else
{
uint8_t x_45; 
lean_free_object(x_1);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_16);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
lean_dec_ref(x_32);
x_49 = l_Lean_MessageData_ofExpr(x_48);
x_50 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_27);
x_52 = l_Lean_MessageData_ofName(x_27);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_28, x_53, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_19 = x_27;
x_20 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_16);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
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
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_16);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_59 = x_32;
} else {
 lean_dec_ref(x_32);
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
}
}
else
{
lean_object* x_61; 
lean_dec(x_26);
lean_inc(x_3);
lean_inc_ref(x_1);
x_61 = l_Lean_Meta_Grind_Arith_Linear_mkCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_73 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1;
x_74 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_73, x_11);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_1);
x_63 = x_3;
x_64 = x_4;
x_65 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_1, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_1, 0);
lean_dec(x_80);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec_ref(x_77);
x_82 = l_Lean_MessageData_ofExpr(x_81);
x_83 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_1, 0, x_82);
lean_inc(x_62);
x_84 = l_Lean_MessageData_ofName(x_62);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_73, x_85, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_dec_ref(x_86);
x_63 = x_3;
x_64 = x_4;
x_65 = lean_box(0);
goto block_72;
}
else
{
uint8_t x_87; 
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_free_object(x_1);
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_77);
if (x_90 == 0)
{
return x_77;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_77, 0);
lean_inc(x_91);
lean_dec(x_77);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_77, 0);
lean_inc(x_93);
lean_dec_ref(x_77);
x_94 = l_Lean_MessageData_ofExpr(x_93);
x_95 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_62);
x_97 = l_Lean_MessageData_ofName(x_62);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_73, x_98, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_99);
x_63 = x_3;
x_64 = x_4;
x_65 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_103 = lean_ctor_get(x_77, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
}
block_72:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_62);
lean_inc(x_18);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___lam__0___boxed), 4, 3);
lean_closure_set(x_66, 0, x_63);
lean_closure_set(x_66, 1, x_18);
lean_closure_set(x_66, 2, x_62);
x_67 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_68 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_67, x_66, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
x_19 = x_62;
x_20 = lean_box(0);
goto block_25;
}
else
{
uint8_t x_69; 
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_16);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_61);
if (x_106 == 0)
{
return x_61;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_61, 0);
lean_inc(x_107);
lean_dec(x_61);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
block_25:
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 1;
x_22 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
if (lean_is_scalar(x_16)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_16;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_109; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_14);
if (x_109 == 0)
{
return x_14;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_14, 0);
lean_inc(x_110);
lean_dec(x_14);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_1, x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__12(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7_spec__11_spec__12___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_Lean_Grind_Linarith_Poly_leadCoeff(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_26 = lean_int_dec_lt(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
x_15 = x_2;
goto block_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0;
lean_inc(x_23);
x_28 = l_Lean_Grind_Linarith_Poly_mul(x_23, x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_15 = x_30;
goto block_22;
}
block_22:
{
lean_object* x_16; 
lean_inc(x_4);
x_16 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 41);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = l_Lean_PersistentArray_push___redArg(x_25, x_2);
lean_ctor_set(x_23, 41, x_28);
x_29 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
x_32 = lean_ctor_get(x_23, 2);
x_33 = lean_ctor_get(x_23, 3);
x_34 = lean_ctor_get(x_23, 4);
x_35 = lean_ctor_get(x_23, 5);
x_36 = lean_ctor_get(x_23, 6);
x_37 = lean_ctor_get(x_23, 7);
x_38 = lean_ctor_get(x_23, 8);
x_39 = lean_ctor_get(x_23, 9);
x_40 = lean_ctor_get(x_23, 10);
x_41 = lean_ctor_get(x_23, 11);
x_42 = lean_ctor_get(x_23, 12);
x_43 = lean_ctor_get(x_23, 13);
x_44 = lean_ctor_get(x_23, 14);
x_45 = lean_ctor_get(x_23, 15);
x_46 = lean_ctor_get(x_23, 16);
x_47 = lean_ctor_get(x_23, 17);
x_48 = lean_ctor_get(x_23, 18);
x_49 = lean_ctor_get(x_23, 19);
x_50 = lean_ctor_get(x_23, 20);
x_51 = lean_ctor_get(x_23, 21);
x_52 = lean_ctor_get(x_23, 22);
x_53 = lean_ctor_get(x_23, 23);
x_54 = lean_ctor_get(x_23, 24);
x_55 = lean_ctor_get(x_23, 25);
x_56 = lean_ctor_get(x_23, 26);
x_57 = lean_ctor_get(x_23, 27);
x_58 = lean_ctor_get(x_23, 28);
x_59 = lean_ctor_get(x_23, 29);
x_60 = lean_ctor_get(x_23, 30);
x_61 = lean_ctor_get(x_23, 31);
x_62 = lean_ctor_get(x_23, 32);
x_63 = lean_ctor_get(x_23, 33);
x_64 = lean_ctor_get(x_23, 34);
x_65 = lean_ctor_get(x_23, 35);
x_66 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_67 = lean_ctor_get(x_23, 36);
x_68 = lean_ctor_get(x_23, 37);
x_69 = lean_ctor_get(x_23, 38);
x_70 = lean_ctor_get(x_23, 39);
x_71 = lean_ctor_get(x_23, 40);
x_72 = lean_ctor_get(x_23, 41);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
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
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
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
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_73 = lean_box(0);
x_74 = lean_array_fset(x_4, x_1, x_73);
x_75 = l_Lean_PersistentArray_push___redArg(x_72, x_2);
x_76 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_31);
lean_ctor_set(x_76, 2, x_32);
lean_ctor_set(x_76, 3, x_33);
lean_ctor_set(x_76, 4, x_34);
lean_ctor_set(x_76, 5, x_35);
lean_ctor_set(x_76, 6, x_36);
lean_ctor_set(x_76, 7, x_37);
lean_ctor_set(x_76, 8, x_38);
lean_ctor_set(x_76, 9, x_39);
lean_ctor_set(x_76, 10, x_40);
lean_ctor_set(x_76, 11, x_41);
lean_ctor_set(x_76, 12, x_42);
lean_ctor_set(x_76, 13, x_43);
lean_ctor_set(x_76, 14, x_44);
lean_ctor_set(x_76, 15, x_45);
lean_ctor_set(x_76, 16, x_46);
lean_ctor_set(x_76, 17, x_47);
lean_ctor_set(x_76, 18, x_48);
lean_ctor_set(x_76, 19, x_49);
lean_ctor_set(x_76, 20, x_50);
lean_ctor_set(x_76, 21, x_51);
lean_ctor_set(x_76, 22, x_52);
lean_ctor_set(x_76, 23, x_53);
lean_ctor_set(x_76, 24, x_54);
lean_ctor_set(x_76, 25, x_55);
lean_ctor_set(x_76, 26, x_56);
lean_ctor_set(x_76, 27, x_57);
lean_ctor_set(x_76, 28, x_58);
lean_ctor_set(x_76, 29, x_59);
lean_ctor_set(x_76, 30, x_60);
lean_ctor_set(x_76, 31, x_61);
lean_ctor_set(x_76, 32, x_62);
lean_ctor_set(x_76, 33, x_63);
lean_ctor_set(x_76, 34, x_64);
lean_ctor_set(x_76, 35, x_65);
lean_ctor_set(x_76, 36, x_67);
lean_ctor_set(x_76, 37, x_68);
lean_ctor_set(x_76, 38, x_69);
lean_ctor_set(x_76, 39, x_70);
lean_ctor_set(x_76, 40, x_71);
lean_ctor_set(x_76, 41, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*42, x_66);
x_77 = lean_array_fset(x_74, x_1, x_76);
lean_ctor_set(x_3, 0, x_77);
return x_3;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
x_78 = lean_array_fget(x_4, x_1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_78, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 8);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 9);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 11);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 12);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 13);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 14);
lean_inc(x_93);
x_94 = lean_ctor_get(x_78, 15);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 16);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 17);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_78, 18);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_78, 19);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 20);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 21);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 22);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_78, 23);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_78, 24);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_78, 25);
lean_inc(x_104);
x_105 = lean_ctor_get(x_78, 26);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 27);
lean_inc(x_106);
x_107 = lean_ctor_get(x_78, 28);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_78, 29);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_78, 30);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_78, 31);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_78, 32);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_78, 33);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_78, 34);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_78, 35);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_78, sizeof(void*)*42);
x_116 = lean_ctor_get(x_78, 36);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 37);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_78, 38);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_78, 39);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 40);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_78, 41);
lean_inc_ref(x_121);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 lean_ctor_release(x_78, 9);
 lean_ctor_release(x_78, 10);
 lean_ctor_release(x_78, 11);
 lean_ctor_release(x_78, 12);
 lean_ctor_release(x_78, 13);
 lean_ctor_release(x_78, 14);
 lean_ctor_release(x_78, 15);
 lean_ctor_release(x_78, 16);
 lean_ctor_release(x_78, 17);
 lean_ctor_release(x_78, 18);
 lean_ctor_release(x_78, 19);
 lean_ctor_release(x_78, 20);
 lean_ctor_release(x_78, 21);
 lean_ctor_release(x_78, 22);
 lean_ctor_release(x_78, 23);
 lean_ctor_release(x_78, 24);
 lean_ctor_release(x_78, 25);
 lean_ctor_release(x_78, 26);
 lean_ctor_release(x_78, 27);
 lean_ctor_release(x_78, 28);
 lean_ctor_release(x_78, 29);
 lean_ctor_release(x_78, 30);
 lean_ctor_release(x_78, 31);
 lean_ctor_release(x_78, 32);
 lean_ctor_release(x_78, 33);
 lean_ctor_release(x_78, 34);
 lean_ctor_release(x_78, 35);
 lean_ctor_release(x_78, 36);
 lean_ctor_release(x_78, 37);
 lean_ctor_release(x_78, 38);
 lean_ctor_release(x_78, 39);
 lean_ctor_release(x_78, 40);
 lean_ctor_release(x_78, 41);
 x_122 = x_78;
} else {
 lean_dec_ref(x_78);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
x_124 = lean_array_fset(x_4, x_1, x_123);
x_125 = l_Lean_PersistentArray_push___redArg(x_121, x_2);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 42, 1);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_79);
lean_ctor_set(x_126, 1, x_80);
lean_ctor_set(x_126, 2, x_81);
lean_ctor_set(x_126, 3, x_82);
lean_ctor_set(x_126, 4, x_83);
lean_ctor_set(x_126, 5, x_84);
lean_ctor_set(x_126, 6, x_85);
lean_ctor_set(x_126, 7, x_86);
lean_ctor_set(x_126, 8, x_87);
lean_ctor_set(x_126, 9, x_88);
lean_ctor_set(x_126, 10, x_89);
lean_ctor_set(x_126, 11, x_90);
lean_ctor_set(x_126, 12, x_91);
lean_ctor_set(x_126, 13, x_92);
lean_ctor_set(x_126, 14, x_93);
lean_ctor_set(x_126, 15, x_94);
lean_ctor_set(x_126, 16, x_95);
lean_ctor_set(x_126, 17, x_96);
lean_ctor_set(x_126, 18, x_97);
lean_ctor_set(x_126, 19, x_98);
lean_ctor_set(x_126, 20, x_99);
lean_ctor_set(x_126, 21, x_100);
lean_ctor_set(x_126, 22, x_101);
lean_ctor_set(x_126, 23, x_102);
lean_ctor_set(x_126, 24, x_103);
lean_ctor_set(x_126, 25, x_104);
lean_ctor_set(x_126, 26, x_105);
lean_ctor_set(x_126, 27, x_106);
lean_ctor_set(x_126, 28, x_107);
lean_ctor_set(x_126, 29, x_108);
lean_ctor_set(x_126, 30, x_109);
lean_ctor_set(x_126, 31, x_110);
lean_ctor_set(x_126, 32, x_111);
lean_ctor_set(x_126, 33, x_112);
lean_ctor_set(x_126, 34, x_113);
lean_ctor_set(x_126, 35, x_114);
lean_ctor_set(x_126, 36, x_116);
lean_ctor_set(x_126, 37, x_117);
lean_ctor_set(x_126, 38, x_118);
lean_ctor_set(x_126, 39, x_119);
lean_ctor_set(x_126, 40, x_120);
lean_ctor_set(x_126, 41, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*42, x_115);
x_127 = lean_array_fset(x_124, x_1, x_126);
x_128 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_5);
lean_ctor_set(x_128, 2, x_6);
lean_ctor_set(x_128, 3, x_7);
lean_ctor_set(x_128, 4, x_8);
lean_ctor_set(x_128, 5, x_9);
lean_ctor_set(x_128, 6, x_10);
lean_ctor_set(x_128, 7, x_11);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_14, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_24 = lean_int_dec_lt(x_13, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_nat_abs(x_13);
lean_dec(x_13);
x_26 = l_Nat_reprFast(x_25);
x_15 = x_26;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_nat_abs(x_13);
lean_dec(x_13);
x_28 = lean_nat_sub(x_27, x_21);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_30 = lean_nat_add(x_28, x_21);
lean_dec(x_28);
x_31 = l_Nat_reprFast(x_30);
x_32 = lean_string_append(x_29, x_31);
lean_dec_ref(x_31);
x_15 = x_32;
goto block_20;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_34 = lean_int_dec_lt(x_13, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_nat_abs(x_13);
lean_dec(x_13);
x_36 = l_Nat_reprFast(x_35);
x_7 = x_36;
goto block_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_nat_abs(x_13);
lean_dec(x_13);
x_38 = lean_nat_sub(x_37, x_21);
lean_dec(x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_40 = lean_nat_add(x_38, x_21);
lean_dec(x_38);
x_41 = l_Nat_reprFast(x_40);
x_42 = lean_string_append(x_39, x_41);
lean_dec_ref(x_41);
x_7 = x_42;
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
if (lean_is_scalar(x_6)) {
 x_10 = lean_alloc_ctor(1, 2, 0);
} else {
 x_10 = x_6;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_5;
x_2 = x_10;
goto _start;
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Nat_reprFast(x_14);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_7 = x_19;
goto block_12;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", diseqs: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Lean_Meta_Grind_Arith_Linear_geAvoiding_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("v: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", upper: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", lower, upper: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", **ignore diseq**, diseqs: ", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", lower: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_Arith_Linear_getBestUpper_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_Linear_getDiseqValues(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_53 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_52, x_11);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
x_57 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_56, x_19);
x_58 = lean_unbox(x_54);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_19);
x_59 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_80; lean_object* x_86; uint8_t x_87; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
x_62 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_dec_eq(x_61, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_89 = lean_int_dec_lt(x_60, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_nat_abs(x_60);
lean_dec(x_60);
x_91 = l_Nat_reprFast(x_90);
x_80 = x_91;
goto block_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_nat_abs(x_60);
lean_dec(x_60);
x_93 = lean_nat_sub(x_92, x_86);
lean_dec(x_92);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_95 = lean_nat_add(x_93, x_86);
lean_dec(x_93);
x_96 = l_Nat_reprFast(x_95);
x_97 = lean_string_append(x_94, x_96);
lean_dec_ref(x_96);
x_80 = x_97;
goto block_85;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
lean_dec(x_61);
x_98 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_99 = lean_int_dec_lt(x_60, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_nat_abs(x_60);
lean_dec(x_60);
x_101 = l_Nat_reprFast(x_100);
x_63 = x_101;
goto block_79;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_nat_abs(x_60);
lean_dec(x_60);
x_103 = lean_nat_sub(x_102, x_86);
lean_dec(x_102);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_105 = lean_nat_add(x_103, x_86);
lean_dec(x_103);
x_106 = l_Nat_reprFast(x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec_ref(x_106);
x_63 = x_107;
goto block_79;
}
}
block_79:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(3, 1, 0);
} else {
 x_64 = x_55;
 lean_ctor_set_tag(x_64, 3);
}
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_MessageData_ofFormat(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_array_size(x_19);
x_70 = 0;
x_71 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_69, x_70, x_19);
x_72 = lean_array_to_list(x_71);
x_73 = lean_box(0);
x_74 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_72, x_73);
x_75 = l_Lean_MessageData_ofList(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_52, x_76, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_dec_ref(x_77);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_78;
}
else
{
lean_dec_ref(x_57);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
}
block_85:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Nat_reprFast(x_61);
x_84 = lean_string_append(x_82, x_83);
lean_dec_ref(x_83);
x_63 = x_84;
goto block_79;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_148; 
x_108 = lean_ctor_get(x_17, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_109 = x_17;
} else {
 lean_dec_ref(x_17);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_113 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_112, x_11);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
lean_inc(x_110);
x_116 = l_Rat_floor(x_110);
x_117 = l_Rat_ofInt(x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
x_120 = l_Rat_sub(x_117, x_119);
x_121 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_120, x_19);
x_148 = lean_unbox(x_114);
lean_dec(x_114);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_19);
x_149 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_211; uint8_t x_217; 
x_150 = lean_ctor_get(x_121, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_121, 1);
lean_inc(x_151);
x_152 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_217 = lean_nat_dec_eq(x_151, x_118);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_219 = lean_int_dec_lt(x_150, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_nat_abs(x_150);
lean_dec(x_150);
x_221 = l_Nat_reprFast(x_220);
x_211 = x_221;
goto block_216;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_nat_abs(x_150);
lean_dec(x_150);
x_223 = lean_nat_sub(x_222, x_118);
lean_dec(x_222);
x_224 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_225 = lean_nat_add(x_223, x_118);
lean_dec(x_223);
x_226 = l_Nat_reprFast(x_225);
x_227 = lean_string_append(x_224, x_226);
lean_dec_ref(x_226);
x_211 = x_227;
goto block_216;
}
}
else
{
lean_object* x_228; uint8_t x_229; 
lean_dec(x_151);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_229 = lean_int_dec_lt(x_150, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_nat_abs(x_150);
lean_dec(x_150);
x_231 = l_Nat_reprFast(x_230);
x_153 = x_231;
goto block_210;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_nat_abs(x_150);
lean_dec(x_150);
x_233 = lean_nat_sub(x_232, x_118);
lean_dec(x_232);
x_234 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_235 = lean_nat_add(x_233, x_118);
lean_dec(x_233);
x_236 = l_Nat_reprFast(x_235);
x_237 = lean_string_append(x_234, x_236);
lean_dec_ref(x_236);
x_153 = x_237;
goto block_210;
}
}
block_210:
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_110);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_155 = lean_ctor_get(x_110, 0);
x_156 = lean_ctor_get(x_110, 1);
if (lean_is_scalar(x_109)) {
 x_157 = lean_alloc_ctor(3, 1, 0);
} else {
 x_157 = x_109;
 lean_ctor_set_tag(x_157, 3);
}
lean_ctor_set(x_157, 0, x_153);
x_158 = l_Lean_MessageData_ofFormat(x_157);
lean_ctor_set_tag(x_110, 7);
lean_ctor_set(x_110, 1, x_158);
lean_ctor_set(x_110, 0, x_152);
x_159 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_110);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_nat_dec_eq(x_156, x_118);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_163 = lean_int_dec_lt(x_155, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_nat_abs(x_155);
lean_dec(x_155);
x_165 = l_Nat_reprFast(x_164);
x_140 = x_160;
x_141 = x_156;
x_142 = x_165;
goto block_147;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_nat_abs(x_155);
lean_dec(x_155);
x_167 = lean_nat_sub(x_166, x_118);
lean_dec(x_166);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_169 = lean_nat_add(x_167, x_118);
lean_dec(x_167);
x_170 = l_Nat_reprFast(x_169);
x_171 = lean_string_append(x_168, x_170);
lean_dec_ref(x_170);
x_140 = x_160;
x_141 = x_156;
x_142 = x_171;
goto block_147;
}
}
else
{
lean_object* x_172; uint8_t x_173; 
lean_dec(x_156);
x_172 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_173 = lean_int_dec_lt(x_155, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_nat_abs(x_155);
lean_dec(x_155);
x_175 = l_Nat_reprFast(x_174);
x_122 = x_160;
x_123 = x_175;
goto block_139;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_nat_abs(x_155);
lean_dec(x_155);
x_177 = lean_nat_sub(x_176, x_118);
lean_dec(x_176);
x_178 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_179 = lean_nat_add(x_177, x_118);
lean_dec(x_177);
x_180 = l_Nat_reprFast(x_179);
x_181 = lean_string_append(x_178, x_180);
lean_dec_ref(x_180);
x_122 = x_160;
x_123 = x_181;
goto block_139;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_182 = lean_ctor_get(x_110, 0);
x_183 = lean_ctor_get(x_110, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_110);
if (lean_is_scalar(x_109)) {
 x_184 = lean_alloc_ctor(3, 1, 0);
} else {
 x_184 = x_109;
 lean_ctor_set_tag(x_184, 3);
}
lean_ctor_set(x_184, 0, x_153);
x_185 = l_Lean_MessageData_ofFormat(x_184);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_152);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_nat_dec_eq(x_183, x_118);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_191 = lean_int_dec_lt(x_182, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_nat_abs(x_182);
lean_dec(x_182);
x_193 = l_Nat_reprFast(x_192);
x_140 = x_188;
x_141 = x_183;
x_142 = x_193;
goto block_147;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_nat_abs(x_182);
lean_dec(x_182);
x_195 = lean_nat_sub(x_194, x_118);
lean_dec(x_194);
x_196 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_197 = lean_nat_add(x_195, x_118);
lean_dec(x_195);
x_198 = l_Nat_reprFast(x_197);
x_199 = lean_string_append(x_196, x_198);
lean_dec_ref(x_198);
x_140 = x_188;
x_141 = x_183;
x_142 = x_199;
goto block_147;
}
}
else
{
lean_object* x_200; uint8_t x_201; 
lean_dec(x_183);
x_200 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_201 = lean_int_dec_lt(x_182, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_nat_abs(x_182);
lean_dec(x_182);
x_203 = l_Nat_reprFast(x_202);
x_122 = x_188;
x_123 = x_203;
goto block_139;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_nat_abs(x_182);
lean_dec(x_182);
x_205 = lean_nat_sub(x_204, x_118);
lean_dec(x_204);
x_206 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_207 = lean_nat_add(x_205, x_118);
lean_dec(x_205);
x_208 = l_Nat_reprFast(x_207);
x_209 = lean_string_append(x_206, x_208);
lean_dec_ref(x_208);
x_122 = x_188;
x_123 = x_209;
goto block_139;
}
}
}
}
block_216:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_213 = lean_string_append(x_211, x_212);
x_214 = l_Nat_reprFast(x_151);
x_215 = lean_string_append(x_213, x_214);
lean_dec_ref(x_214);
x_153 = x_215;
goto block_210;
}
}
block_139:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
if (lean_is_scalar(x_115)) {
 x_124 = lean_alloc_ctor(3, 1, 0);
} else {
 x_124 = x_115;
 lean_ctor_set_tag(x_124, 3);
}
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_MessageData_ofFormat(x_124);
if (lean_is_scalar(x_111)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_111;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_size(x_19);
x_130 = 0;
x_131 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_129, x_130, x_19);
x_132 = lean_array_to_list(x_131);
x_133 = lean_box(0);
x_134 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_132, x_133);
x_135 = l_Lean_MessageData_ofList(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_128);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_112, x_136, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec_ref(x_137);
x_138 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_138;
}
else
{
lean_dec_ref(x_121);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_137;
}
}
block_147:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_144 = lean_string_append(x_142, x_143);
x_145 = l_Nat_reprFast(x_141);
x_146 = lean_string_append(x_144, x_145);
lean_dec_ref(x_145);
x_122 = x_140;
x_123 = x_146;
goto block_139;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_238 = lean_ctor_get(x_15, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_239 = x_15;
} else {
 lean_dec_ref(x_15);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_345; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_239);
x_309 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_310 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_309, x_11);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
lean_inc(x_240);
x_313 = l_Rat_ceil(x_240);
x_314 = l_Rat_ofInt(x_313);
x_315 = lean_unsigned_to_nat(1u);
x_316 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0;
x_317 = l_Rat_add(x_314, x_316);
x_318 = l_Lean_Meta_Grind_Arith_Linear_geAvoiding(x_317, x_19);
x_345 = lean_unbox(x_311);
lean_dec(x_311);
if (x_345 == 0)
{
lean_object* x_346; 
lean_dec(x_312);
lean_dec(x_240);
lean_dec(x_19);
x_346 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_318, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_408; uint8_t x_414; 
x_347 = lean_ctor_get(x_318, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_318, 1);
lean_inc(x_348);
x_349 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_414 = lean_nat_dec_eq(x_348, x_315);
if (x_414 == 0)
{
lean_object* x_415; uint8_t x_416; 
x_415 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_416 = lean_int_dec_lt(x_347, x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_nat_abs(x_347);
lean_dec(x_347);
x_418 = l_Nat_reprFast(x_417);
x_408 = x_418;
goto block_413;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_419 = lean_nat_abs(x_347);
lean_dec(x_347);
x_420 = lean_nat_sub(x_419, x_315);
lean_dec(x_419);
x_421 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_422 = lean_nat_add(x_420, x_315);
lean_dec(x_420);
x_423 = l_Nat_reprFast(x_422);
x_424 = lean_string_append(x_421, x_423);
lean_dec_ref(x_423);
x_408 = x_424;
goto block_413;
}
}
else
{
lean_object* x_425; uint8_t x_426; 
lean_dec(x_348);
x_425 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_426 = lean_int_dec_lt(x_347, x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_nat_abs(x_347);
lean_dec(x_347);
x_428 = l_Nat_reprFast(x_427);
x_350 = x_428;
goto block_407;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_429 = lean_nat_abs(x_347);
lean_dec(x_347);
x_430 = lean_nat_sub(x_429, x_315);
lean_dec(x_429);
x_431 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_432 = lean_nat_add(x_430, x_315);
lean_dec(x_430);
x_433 = l_Nat_reprFast(x_432);
x_434 = lean_string_append(x_431, x_433);
lean_dec_ref(x_433);
x_350 = x_434;
goto block_407;
}
}
block_407:
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_240);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_352 = lean_ctor_get(x_240, 0);
x_353 = lean_ctor_get(x_240, 1);
x_354 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_354, 0, x_350);
x_355 = l_Lean_MessageData_ofFormat(x_354);
lean_ctor_set_tag(x_240, 7);
lean_ctor_set(x_240, 1, x_355);
lean_ctor_set(x_240, 0, x_349);
x_356 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_240);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_nat_dec_eq(x_353, x_315);
if (x_358 == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_360 = lean_int_dec_lt(x_352, x_359);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_nat_abs(x_352);
lean_dec(x_352);
x_362 = l_Nat_reprFast(x_361);
x_337 = x_353;
x_338 = x_357;
x_339 = x_362;
goto block_344;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_nat_abs(x_352);
lean_dec(x_352);
x_364 = lean_nat_sub(x_363, x_315);
lean_dec(x_363);
x_365 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_366 = lean_nat_add(x_364, x_315);
lean_dec(x_364);
x_367 = l_Nat_reprFast(x_366);
x_368 = lean_string_append(x_365, x_367);
lean_dec_ref(x_367);
x_337 = x_353;
x_338 = x_357;
x_339 = x_368;
goto block_344;
}
}
else
{
lean_object* x_369; uint8_t x_370; 
lean_dec(x_353);
x_369 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_370 = lean_int_dec_lt(x_352, x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_nat_abs(x_352);
lean_dec(x_352);
x_372 = l_Nat_reprFast(x_371);
x_319 = x_357;
x_320 = x_372;
goto block_336;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_373 = lean_nat_abs(x_352);
lean_dec(x_352);
x_374 = lean_nat_sub(x_373, x_315);
lean_dec(x_373);
x_375 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_376 = lean_nat_add(x_374, x_315);
lean_dec(x_374);
x_377 = l_Nat_reprFast(x_376);
x_378 = lean_string_append(x_375, x_377);
lean_dec_ref(x_377);
x_319 = x_357;
x_320 = x_378;
goto block_336;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_379 = lean_ctor_get(x_240, 0);
x_380 = lean_ctor_get(x_240, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_240);
x_381 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_381, 0, x_350);
x_382 = l_Lean_MessageData_ofFormat(x_381);
x_383 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_383, 0, x_349);
lean_ctor_set(x_383, 1, x_382);
x_384 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
x_385 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_nat_dec_eq(x_380, x_315);
if (x_386 == 0)
{
lean_object* x_387; uint8_t x_388; 
x_387 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_388 = lean_int_dec_lt(x_379, x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_nat_abs(x_379);
lean_dec(x_379);
x_390 = l_Nat_reprFast(x_389);
x_337 = x_380;
x_338 = x_385;
x_339 = x_390;
goto block_344;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_391 = lean_nat_abs(x_379);
lean_dec(x_379);
x_392 = lean_nat_sub(x_391, x_315);
lean_dec(x_391);
x_393 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_394 = lean_nat_add(x_392, x_315);
lean_dec(x_392);
x_395 = l_Nat_reprFast(x_394);
x_396 = lean_string_append(x_393, x_395);
lean_dec_ref(x_395);
x_337 = x_380;
x_338 = x_385;
x_339 = x_396;
goto block_344;
}
}
else
{
lean_object* x_397; uint8_t x_398; 
lean_dec(x_380);
x_397 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_398 = lean_int_dec_lt(x_379, x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_nat_abs(x_379);
lean_dec(x_379);
x_400 = l_Nat_reprFast(x_399);
x_319 = x_385;
x_320 = x_400;
goto block_336;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_nat_abs(x_379);
lean_dec(x_379);
x_402 = lean_nat_sub(x_401, x_315);
lean_dec(x_401);
x_403 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_404 = lean_nat_add(x_402, x_315);
lean_dec(x_402);
x_405 = l_Nat_reprFast(x_404);
x_406 = lean_string_append(x_403, x_405);
lean_dec_ref(x_405);
x_319 = x_385;
x_320 = x_406;
goto block_336;
}
}
}
}
block_413:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_410 = lean_string_append(x_408, x_409);
x_411 = l_Nat_reprFast(x_348);
x_412 = lean_string_append(x_410, x_411);
lean_dec_ref(x_411);
x_350 = x_412;
goto block_407;
}
}
block_336:
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; size_t x_326; size_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
if (lean_is_scalar(x_312)) {
 x_321 = lean_alloc_ctor(3, 1, 0);
} else {
 x_321 = x_312;
 lean_ctor_set_tag(x_321, 3);
}
lean_ctor_set(x_321, 0, x_320);
x_322 = l_Lean_MessageData_ofFormat(x_321);
x_323 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_322);
x_324 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_array_size(x_19);
x_327 = 0;
x_328 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_326, x_327, x_19);
x_329 = lean_array_to_list(x_328);
x_330 = lean_box(0);
x_331 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_329, x_330);
x_332 = l_Lean_MessageData_ofList(x_331);
x_333 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_333, 0, x_325);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_309, x_333, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; 
lean_dec_ref(x_334);
x_335 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_318, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_335;
}
else
{
lean_dec_ref(x_318);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_334;
}
}
block_344:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_341 = lean_string_append(x_339, x_340);
x_342 = l_Nat_reprFast(x_337);
x_343 = lean_string_append(x_341, x_342);
lean_dec_ref(x_342);
x_319 = x_338;
x_320 = x_343;
goto block_336;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_590; uint8_t x_622; uint8_t x_708; 
x_435 = lean_ctor_get(x_17, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_436 = x_17;
} else {
 lean_dec_ref(x_17);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_435, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_439 = x_435;
} else {
 lean_dec_ref(x_435);
 x_439 = lean_box(0);
}
lean_inc(x_240);
lean_inc(x_437);
x_708 = l_Rat_blt(x_437, x_240);
if (x_708 == 0)
{
uint8_t x_709; 
x_709 = l_instDecidableEqRat_decEq(x_240, x_437);
if (x_709 == 0)
{
x_622 = x_709;
goto block_707;
}
else
{
uint8_t x_710; 
x_710 = lean_ctor_get_uint8(x_241, sizeof(void*)*2);
if (x_710 == 0)
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_438, sizeof(void*)*2);
x_622 = x_711;
goto block_707;
}
else
{
lean_object* x_712; 
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
x_712 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_241, x_438, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_712;
}
}
}
else
{
x_622 = x_708;
goto block_707;
}
block_503:
{
uint8_t x_445; 
x_445 = !lean_is_exclusive(x_437);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_446 = lean_ctor_get(x_437, 0);
x_447 = lean_ctor_get(x_437, 1);
if (lean_is_scalar(x_436)) {
 x_448 = lean_alloc_ctor(3, 1, 0);
} else {
 x_448 = x_436;
 lean_ctor_set_tag(x_448, 3);
}
lean_ctor_set(x_448, 0, x_444);
x_449 = l_Lean_MessageData_ofFormat(x_448);
lean_ctor_set_tag(x_437, 7);
lean_ctor_set(x_437, 1, x_449);
lean_ctor_set(x_437, 0, x_443);
x_450 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
if (lean_is_scalar(x_439)) {
 x_451 = lean_alloc_ctor(7, 2, 0);
} else {
 x_451 = x_439;
 lean_ctor_set_tag(x_451, 7);
}
lean_ctor_set(x_451, 0, x_437);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_nat_dec_eq(x_447, x_452);
if (x_453 == 0)
{
lean_object* x_454; uint8_t x_455; 
x_454 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_455 = lean_int_dec_lt(x_446, x_454);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_nat_abs(x_446);
lean_dec(x_446);
x_457 = l_Nat_reprFast(x_456);
x_41 = lean_box(0);
x_42 = x_441;
x_43 = x_451;
x_44 = x_442;
x_45 = x_447;
x_46 = x_457;
goto block_51;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_458 = lean_nat_abs(x_446);
lean_dec(x_446);
x_459 = lean_nat_sub(x_458, x_452);
lean_dec(x_458);
x_460 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_461 = lean_nat_add(x_459, x_452);
lean_dec(x_459);
x_462 = l_Nat_reprFast(x_461);
x_463 = lean_string_append(x_460, x_462);
lean_dec_ref(x_462);
x_41 = lean_box(0);
x_42 = x_441;
x_43 = x_451;
x_44 = x_442;
x_45 = x_447;
x_46 = x_463;
goto block_51;
}
}
else
{
lean_object* x_464; uint8_t x_465; 
lean_dec(x_447);
x_464 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_465 = lean_int_dec_lt(x_446, x_464);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_nat_abs(x_446);
lean_dec(x_446);
x_467 = l_Nat_reprFast(x_466);
x_20 = lean_box(0);
x_21 = x_441;
x_22 = x_442;
x_23 = x_451;
x_24 = x_467;
goto block_40;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_468 = lean_nat_abs(x_446);
lean_dec(x_446);
x_469 = lean_nat_sub(x_468, x_452);
lean_dec(x_468);
x_470 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_471 = lean_nat_add(x_469, x_452);
lean_dec(x_469);
x_472 = l_Nat_reprFast(x_471);
x_473 = lean_string_append(x_470, x_472);
lean_dec_ref(x_472);
x_20 = lean_box(0);
x_21 = x_441;
x_22 = x_442;
x_23 = x_451;
x_24 = x_473;
goto block_40;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_474 = lean_ctor_get(x_437, 0);
x_475 = lean_ctor_get(x_437, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_437);
if (lean_is_scalar(x_436)) {
 x_476 = lean_alloc_ctor(3, 1, 0);
} else {
 x_476 = x_436;
 lean_ctor_set_tag(x_476, 3);
}
lean_ctor_set(x_476, 0, x_444);
x_477 = l_Lean_MessageData_ofFormat(x_476);
x_478 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_478, 0, x_443);
lean_ctor_set(x_478, 1, x_477);
x_479 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7;
if (lean_is_scalar(x_439)) {
 x_480 = lean_alloc_ctor(7, 2, 0);
} else {
 x_480 = x_439;
 lean_ctor_set_tag(x_480, 7);
}
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
x_481 = lean_unsigned_to_nat(1u);
x_482 = lean_nat_dec_eq(x_475, x_481);
if (x_482 == 0)
{
lean_object* x_483; uint8_t x_484; 
x_483 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_484 = lean_int_dec_lt(x_474, x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_nat_abs(x_474);
lean_dec(x_474);
x_486 = l_Nat_reprFast(x_485);
x_41 = lean_box(0);
x_42 = x_441;
x_43 = x_480;
x_44 = x_442;
x_45 = x_475;
x_46 = x_486;
goto block_51;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_487 = lean_nat_abs(x_474);
lean_dec(x_474);
x_488 = lean_nat_sub(x_487, x_481);
lean_dec(x_487);
x_489 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_490 = lean_nat_add(x_488, x_481);
lean_dec(x_488);
x_491 = l_Nat_reprFast(x_490);
x_492 = lean_string_append(x_489, x_491);
lean_dec_ref(x_491);
x_41 = lean_box(0);
x_42 = x_441;
x_43 = x_480;
x_44 = x_442;
x_45 = x_475;
x_46 = x_492;
goto block_51;
}
}
else
{
lean_object* x_493; uint8_t x_494; 
lean_dec(x_475);
x_493 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_494 = lean_int_dec_lt(x_474, x_493);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_nat_abs(x_474);
lean_dec(x_474);
x_496 = l_Nat_reprFast(x_495);
x_20 = lean_box(0);
x_21 = x_441;
x_22 = x_442;
x_23 = x_480;
x_24 = x_496;
goto block_40;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_497 = lean_nat_abs(x_474);
lean_dec(x_474);
x_498 = lean_nat_sub(x_497, x_481);
lean_dec(x_497);
x_499 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_500 = lean_nat_add(x_498, x_481);
lean_dec(x_498);
x_501 = l_Nat_reprFast(x_500);
x_502 = lean_string_append(x_499, x_501);
lean_dec_ref(x_501);
x_20 = lean_box(0);
x_21 = x_441;
x_22 = x_442;
x_23 = x_480;
x_24 = x_502;
goto block_40;
}
}
}
}
block_514:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_510 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_511 = lean_string_append(x_509, x_510);
x_512 = l_Nat_reprFast(x_506);
x_513 = lean_string_append(x_511, x_512);
lean_dec_ref(x_512);
x_440 = lean_box(0);
x_441 = x_505;
x_442 = x_507;
x_443 = x_508;
x_444 = x_513;
goto block_503;
}
block_578:
{
uint8_t x_520; 
x_520 = !lean_is_exclusive(x_240);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; 
x_521 = lean_ctor_get(x_240, 0);
x_522 = lean_ctor_get(x_240, 1);
x_523 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_523, 0, x_519);
x_524 = l_Lean_MessageData_ofFormat(x_523);
lean_ctor_set_tag(x_240, 7);
lean_ctor_set(x_240, 1, x_524);
lean_ctor_set(x_240, 0, x_516);
x_525 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
x_526 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_526, 0, x_240);
lean_ctor_set(x_526, 1, x_525);
x_527 = lean_unsigned_to_nat(1u);
x_528 = lean_nat_dec_eq(x_522, x_527);
if (x_528 == 0)
{
lean_object* x_529; uint8_t x_530; 
x_529 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_530 = lean_int_dec_lt(x_521, x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_nat_abs(x_521);
lean_dec(x_521);
x_532 = l_Nat_reprFast(x_531);
x_504 = lean_box(0);
x_505 = x_517;
x_506 = x_522;
x_507 = x_518;
x_508 = x_526;
x_509 = x_532;
goto block_514;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_533 = lean_nat_abs(x_521);
lean_dec(x_521);
x_534 = lean_nat_sub(x_533, x_527);
lean_dec(x_533);
x_535 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_536 = lean_nat_add(x_534, x_527);
lean_dec(x_534);
x_537 = l_Nat_reprFast(x_536);
x_538 = lean_string_append(x_535, x_537);
lean_dec_ref(x_537);
x_504 = lean_box(0);
x_505 = x_517;
x_506 = x_522;
x_507 = x_518;
x_508 = x_526;
x_509 = x_538;
goto block_514;
}
}
else
{
lean_object* x_539; uint8_t x_540; 
lean_dec(x_522);
x_539 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_540 = lean_int_dec_lt(x_521, x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_nat_abs(x_521);
lean_dec(x_521);
x_542 = l_Nat_reprFast(x_541);
x_440 = lean_box(0);
x_441 = x_517;
x_442 = x_518;
x_443 = x_526;
x_444 = x_542;
goto block_503;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_543 = lean_nat_abs(x_521);
lean_dec(x_521);
x_544 = lean_nat_sub(x_543, x_527);
lean_dec(x_543);
x_545 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_546 = lean_nat_add(x_544, x_527);
lean_dec(x_544);
x_547 = l_Nat_reprFast(x_546);
x_548 = lean_string_append(x_545, x_547);
lean_dec_ref(x_547);
x_440 = lean_box(0);
x_441 = x_517;
x_442 = x_518;
x_443 = x_526;
x_444 = x_548;
goto block_503;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_549 = lean_ctor_get(x_240, 0);
x_550 = lean_ctor_get(x_240, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_240);
x_551 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_551, 0, x_519);
x_552 = l_Lean_MessageData_ofFormat(x_551);
x_553 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_553, 0, x_516);
lean_ctor_set(x_553, 1, x_552);
x_554 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13;
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = lean_unsigned_to_nat(1u);
x_557 = lean_nat_dec_eq(x_550, x_556);
if (x_557 == 0)
{
lean_object* x_558; uint8_t x_559; 
x_558 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_559 = lean_int_dec_lt(x_549, x_558);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_nat_abs(x_549);
lean_dec(x_549);
x_561 = l_Nat_reprFast(x_560);
x_504 = lean_box(0);
x_505 = x_517;
x_506 = x_550;
x_507 = x_518;
x_508 = x_555;
x_509 = x_561;
goto block_514;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_562 = lean_nat_abs(x_549);
lean_dec(x_549);
x_563 = lean_nat_sub(x_562, x_556);
lean_dec(x_562);
x_564 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_565 = lean_nat_add(x_563, x_556);
lean_dec(x_563);
x_566 = l_Nat_reprFast(x_565);
x_567 = lean_string_append(x_564, x_566);
lean_dec_ref(x_566);
x_504 = lean_box(0);
x_505 = x_517;
x_506 = x_550;
x_507 = x_518;
x_508 = x_555;
x_509 = x_567;
goto block_514;
}
}
else
{
lean_object* x_568; uint8_t x_569; 
lean_dec(x_550);
x_568 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_569 = lean_int_dec_lt(x_549, x_568);
if (x_569 == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_nat_abs(x_549);
lean_dec(x_549);
x_571 = l_Nat_reprFast(x_570);
x_440 = lean_box(0);
x_441 = x_517;
x_442 = x_518;
x_443 = x_555;
x_444 = x_571;
goto block_503;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_572 = lean_nat_abs(x_549);
lean_dec(x_549);
x_573 = lean_nat_sub(x_572, x_556);
lean_dec(x_572);
x_574 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_575 = lean_nat_add(x_573, x_556);
lean_dec(x_573);
x_576 = l_Nat_reprFast(x_575);
x_577 = lean_string_append(x_574, x_576);
lean_dec_ref(x_576);
x_440 = lean_box(0);
x_441 = x_517;
x_442 = x_518;
x_443 = x_555;
x_444 = x_577;
goto block_503;
}
}
}
}
block_589:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_585 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_586 = lean_string_append(x_584, x_585);
x_587 = l_Nat_reprFast(x_581);
x_588 = lean_string_append(x_586, x_587);
lean_dec_ref(x_587);
x_515 = lean_box(0);
x_516 = x_579;
x_517 = x_582;
x_518 = x_583;
x_519 = x_588;
goto block_578;
}
block_621:
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_591 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_592 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_591, x_11);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec_ref(x_592);
x_594 = lean_unbox(x_593);
lean_dec(x_593);
if (x_594 == 0)
{
lean_object* x_595; 
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_240);
lean_dec(x_19);
x_595 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_590, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_596 = lean_ctor_get(x_590, 0);
x_597 = lean_ctor_get(x_590, 1);
x_598 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_599 = lean_unsigned_to_nat(1u);
x_600 = lean_nat_dec_eq(x_597, x_599);
if (x_600 == 0)
{
lean_object* x_601; uint8_t x_602; 
lean_inc(x_597);
x_601 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_602 = lean_int_dec_lt(x_596, x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_nat_abs(x_596);
x_604 = l_Nat_reprFast(x_603);
x_579 = x_598;
x_580 = lean_box(0);
x_581 = x_597;
x_582 = x_590;
x_583 = x_591;
x_584 = x_604;
goto block_589;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_605 = lean_nat_abs(x_596);
x_606 = lean_nat_sub(x_605, x_599);
lean_dec(x_605);
x_607 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_608 = lean_nat_add(x_606, x_599);
lean_dec(x_606);
x_609 = l_Nat_reprFast(x_608);
x_610 = lean_string_append(x_607, x_609);
lean_dec_ref(x_609);
x_579 = x_598;
x_580 = lean_box(0);
x_581 = x_597;
x_582 = x_590;
x_583 = x_591;
x_584 = x_610;
goto block_589;
}
}
else
{
lean_object* x_611; uint8_t x_612; 
x_611 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_612 = lean_int_dec_lt(x_596, x_611);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_nat_abs(x_596);
x_614 = l_Nat_reprFast(x_613);
x_515 = lean_box(0);
x_516 = x_598;
x_517 = x_590;
x_518 = x_591;
x_519 = x_614;
goto block_578;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_615 = lean_nat_abs(x_596);
x_616 = lean_nat_sub(x_615, x_599);
lean_dec(x_615);
x_617 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_618 = lean_nat_add(x_616, x_599);
lean_dec(x_616);
x_619 = l_Nat_reprFast(x_618);
x_620 = lean_string_append(x_617, x_619);
lean_dec_ref(x_619);
x_515 = lean_box(0);
x_516 = x_598;
x_517 = x_590;
x_518 = x_591;
x_519 = x_620;
goto block_578;
}
}
}
}
block_707:
{
if (x_622 == 0)
{
uint8_t x_623; 
x_623 = l_instDecidableEqRat_decEq(x_240, x_437);
if (x_623 == 0)
{
uint8_t x_624; uint8_t x_625; lean_object* x_626; 
lean_dec(x_242);
lean_dec(x_239);
x_624 = lean_ctor_get_uint8(x_241, sizeof(void*)*2);
lean_dec(x_241);
x_625 = lean_ctor_get_uint8(x_438, sizeof(void*)*2);
lean_dec(x_438);
lean_inc(x_437);
lean_inc(x_240);
x_626 = l_Lean_Meta_Grind_Arith_Linear_findInt_x3f(x_240, x_624, x_437, x_625, x_19);
if (lean_obj_tag(x_626) == 1)
{
lean_object* x_627; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
lean_dec_ref(x_626);
x_590 = x_627;
goto block_621;
}
else
{
lean_object* x_628; 
lean_dec(x_626);
lean_inc(x_437);
lean_inc(x_240);
x_628 = l_Lean_Meta_Grind_Arith_Linear_findRat(x_240, x_437, x_19);
x_590 = x_628;
goto block_621;
}
}
else
{
lean_object* x_629; 
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_436);
x_629 = l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f(x_240, x_19);
if (lean_obj_tag(x_629) == 1)
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
x_631 = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; uint8_t x_633; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
lean_dec_ref(x_631);
x_633 = lean_unbox(x_632);
lean_dec(x_632);
if (x_633 == 0)
{
lean_object* x_634; 
lean_dec(x_241);
x_634 = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2(x_630, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_630);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
lean_dec_ref(x_634);
lean_inc(x_3);
x_636 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_processVar___lam__0___boxed), 3, 2);
lean_closure_set(x_636, 0, x_3);
lean_closure_set(x_636, 1, x_635);
x_637 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_638 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_637, x_636, x_4);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; 
lean_dec_ref(x_638);
x_639 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_640 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_639, x_11);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
lean_dec_ref(x_640);
x_642 = lean_unbox(x_641);
lean_dec(x_641);
if (x_642 == 0)
{
lean_object* x_643; 
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_19);
x_643 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_643;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; 
x_644 = lean_ctor_get(x_240, 0);
x_645 = lean_ctor_get(x_240, 1);
x_646 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_647 = lean_unsigned_to_nat(1u);
x_648 = lean_nat_dec_eq(x_645, x_647);
if (x_648 == 0)
{
lean_object* x_649; uint8_t x_650; 
x_649 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_650 = lean_int_dec_lt(x_644, x_649);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_nat_abs(x_644);
x_652 = l_Nat_reprFast(x_651);
lean_inc(x_645);
x_266 = lean_box(0);
x_267 = x_646;
x_268 = x_645;
x_269 = x_639;
x_270 = x_652;
goto block_275;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_653 = lean_nat_abs(x_644);
x_654 = lean_nat_sub(x_653, x_647);
lean_dec(x_653);
x_655 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_656 = lean_nat_add(x_654, x_647);
lean_dec(x_654);
x_657 = l_Nat_reprFast(x_656);
x_658 = lean_string_append(x_655, x_657);
lean_dec_ref(x_657);
lean_inc(x_645);
x_266 = lean_box(0);
x_267 = x_646;
x_268 = x_645;
x_269 = x_639;
x_270 = x_658;
goto block_275;
}
}
else
{
lean_object* x_659; uint8_t x_660; 
x_659 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_660 = lean_int_dec_lt(x_644, x_659);
if (x_660 == 0)
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_nat_abs(x_644);
x_662 = l_Nat_reprFast(x_661);
x_243 = lean_box(0);
x_244 = x_646;
x_245 = x_639;
x_246 = x_662;
goto block_265;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_663 = lean_nat_abs(x_644);
x_664 = lean_nat_sub(x_663, x_647);
lean_dec(x_663);
x_665 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_666 = lean_nat_add(x_664, x_647);
lean_dec(x_664);
x_667 = l_Nat_reprFast(x_666);
x_668 = lean_string_append(x_665, x_667);
lean_dec_ref(x_667);
x_243 = lean_box(0);
x_244 = x_646;
x_245 = x_639;
x_246 = x_668;
goto block_265;
}
}
}
}
else
{
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_638;
}
}
else
{
uint8_t x_669; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_669 = !lean_is_exclusive(x_634);
if (x_669 == 0)
{
return x_634;
}
else
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_634, 0);
lean_inc(x_670);
lean_dec(x_634);
x_671 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_671, 0, x_670);
return x_671;
}
}
}
else
{
lean_object* x_672; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
x_672 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict(x_241, x_630, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_672;
}
}
else
{
uint8_t x_673; 
lean_dec(x_630);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_673 = !lean_is_exclusive(x_631);
if (x_673 == 0)
{
return x_631;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = lean_ctor_get(x_631, 0);
lean_inc(x_674);
lean_dec(x_631);
x_675 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_675, 0, x_674);
return x_675;
}
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; 
lean_dec(x_629);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_239);
x_676 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_677 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_676, x_11);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
lean_dec_ref(x_677);
x_679 = lean_unbox(x_678);
lean_dec(x_678);
if (x_679 == 0)
{
lean_object* x_680; 
lean_dec(x_19);
x_680 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_681 = lean_ctor_get(x_240, 0);
x_682 = lean_ctor_get(x_240, 1);
x_683 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5;
x_684 = lean_unsigned_to_nat(1u);
x_685 = lean_nat_dec_eq(x_682, x_684);
if (x_685 == 0)
{
lean_object* x_686; uint8_t x_687; 
x_686 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_687 = lean_int_dec_lt(x_681, x_686);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; 
x_688 = lean_nat_abs(x_681);
x_689 = l_Nat_reprFast(x_688);
lean_inc(x_682);
x_299 = x_683;
x_300 = x_676;
x_301 = x_682;
x_302 = lean_box(0);
x_303 = x_689;
goto block_308;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_690 = lean_nat_abs(x_681);
x_691 = lean_nat_sub(x_690, x_684);
lean_dec(x_690);
x_692 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_693 = lean_nat_add(x_691, x_684);
lean_dec(x_691);
x_694 = l_Nat_reprFast(x_693);
x_695 = lean_string_append(x_692, x_694);
lean_dec_ref(x_694);
lean_inc(x_682);
x_299 = x_683;
x_300 = x_676;
x_301 = x_682;
x_302 = lean_box(0);
x_303 = x_695;
goto block_308;
}
}
else
{
lean_object* x_696; uint8_t x_697; 
x_696 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_697 = lean_int_dec_lt(x_681, x_696);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_nat_abs(x_681);
x_699 = l_Nat_reprFast(x_698);
x_276 = x_683;
x_277 = x_676;
x_278 = lean_box(0);
x_279 = x_699;
goto block_298;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_700 = lean_nat_abs(x_681);
x_701 = lean_nat_sub(x_700, x_684);
lean_dec(x_700);
x_702 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10;
x_703 = lean_nat_add(x_701, x_684);
lean_dec(x_701);
x_704 = l_Nat_reprFast(x_703);
x_705 = lean_string_append(x_702, x_704);
lean_dec_ref(x_704);
x_276 = x_683;
x_277 = x_676;
x_278 = lean_box(0);
x_279 = x_705;
goto block_298;
}
}
}
}
}
}
else
{
lean_object* x_706; 
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_19);
x_706 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict(x_241, x_438, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_706;
}
}
}
block_265:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; size_t x_255; size_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
if (lean_is_scalar(x_239)) {
 x_247 = lean_alloc_ctor(3, 1, 0);
} else {
 x_247 = x_239;
 lean_ctor_set_tag(x_247, 3);
}
lean_ctor_set(x_247, 0, x_246);
x_248 = l_Lean_MessageData_ofFormat(x_247);
lean_inc_ref(x_248);
if (lean_is_scalar(x_242)) {
 x_249 = lean_alloc_ctor(7, 2, 0);
} else {
 x_249 = x_242;
 lean_ctor_set_tag(x_249, 7);
}
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9;
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
x_253 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11;
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_array_size(x_19);
x_256 = 0;
x_257 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_255, x_256, x_19);
x_258 = lean_array_to_list(x_257);
x_259 = lean_box(0);
x_260 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_258, x_259);
x_261 = l_Lean_MessageData_ofList(x_260);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_254);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_245, x_262, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
lean_dec_ref(x_263);
x_264 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_264;
}
else
{
lean_dec(x_240);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_263;
}
}
block_275:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_272 = lean_string_append(x_270, x_271);
x_273 = l_Nat_reprFast(x_268);
x_274 = lean_string_append(x_272, x_273);
lean_dec_ref(x_273);
x_243 = lean_box(0);
x_244 = x_267;
x_245 = x_269;
x_246 = x_274;
goto block_265;
}
block_298:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; size_t x_288; size_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_280 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = l_Lean_MessageData_ofFormat(x_280);
lean_inc_ref(x_281);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_276);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9;
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_281);
x_286 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_array_size(x_19);
x_289 = 0;
x_290 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_288, x_289, x_19);
x_291 = lean_array_to_list(x_290);
x_292 = lean_box(0);
x_293 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_291, x_292);
x_294 = l_Lean_MessageData_ofList(x_293);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_287);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_277, x_295, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
lean_dec_ref(x_296);
x_297 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_297;
}
else
{
lean_dec(x_240);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_296;
}
}
block_308:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_305 = lean_string_append(x_303, x_304);
x_306 = l_Nat_reprFast(x_301);
x_307 = lean_string_append(x_305, x_306);
lean_dec_ref(x_306);
x_276 = x_299;
x_277 = x_300;
x_278 = lean_box(0);
x_279 = x_307;
goto block_298;
}
}
block_40:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_size(x_19);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__0(x_30, x_31, x_19);
x_33 = lean_array_to_list(x_32);
x_34 = lean_box(0);
x_35 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_33, x_34);
x_36 = l_Lean_MessageData_ofList(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_22, x_37, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_setAssignment(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_dec_ref(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
}
block_51:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Nat_reprFast(x_45);
x_50 = lean_string_append(x_48, x_49);
lean_dec_ref(x_49);
x_20 = lean_box(0);
x_21 = x_42;
x_22 = x_44;
x_23 = x_43;
x_24 = x_50;
goto block_40;
}
}
else
{
uint8_t x_713; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_713 = !lean_is_exclusive(x_18);
if (x_713 == 0)
{
return x_18;
}
else
{
lean_object* x_714; lean_object* x_715; 
x_714 = lean_ctor_get(x_18, 0);
lean_inc(x_714);
lean_dec(x_18);
x_715 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_715, 0, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_716 = !lean_is_exclusive(x_16);
if (x_716 == 0)
{
return x_16;
}
else
{
lean_object* x_717; lean_object* x_718; 
x_717 = lean_ctor_get(x_16, 0);
lean_inc(x_717);
lean_dec(x_16);
x_718 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_718, 0, x_717);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_719 = !lean_is_exclusive(x_14);
if (x_719 == 0)
{
return x_14;
}
else
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_14, 0);
lean_inc(x_720);
lean_dec(x_14);
x_721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_721, 0, x_720);
return x_721;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 30);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_17, 35);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec_ref(x_15);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_box(x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_23, 35);
lean_inc_ref(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_15, 2);
lean_inc(x_25);
lean_dec_ref(x_15);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0;
x_15 = l_ReaderT_instMonad___redArg(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 1);
lean_dec(x_24);
x_25 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1;
x_26 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2;
lean_inc_ref(x_20);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_27, 0, x_20);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_23);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_22);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_32, 0, x_21);
lean_ctor_set(x_17, 4, x_30);
lean_ctor_set(x_17, 3, x_31);
lean_ctor_set(x_17, 2, x_32);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set(x_15, 1, x_26);
x_33 = l_ReaderT_instMonad___redArg(x_15);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_42 = lean_ctor_get(x_35, 1);
lean_dec(x_42);
x_43 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
x_44 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_inc_ref(x_38);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_40);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_50, 0, x_39);
lean_ctor_set(x_35, 4, x_48);
lean_ctor_set(x_35, 3, x_49);
lean_ctor_set(x_35, 2, x_50);
lean_ctor_set(x_35, 1, x_43);
lean_ctor_set(x_35, 0, x_47);
lean_ctor_set(x_33, 1, x_44);
x_51 = l_ReaderT_instMonad___redArg(x_33);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_59 = l_instInhabitedOfMonad___redArg(x_57, x_58);
x_60 = lean_panic_fn(x_59, x_1);
x_61 = lean_apply_12(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_62 = lean_ctor_get(x_35, 0);
x_63 = lean_ctor_get(x_35, 2);
x_64 = lean_ctor_get(x_35, 3);
x_65 = lean_ctor_get(x_35, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_35);
x_66 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
x_67 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_inc_ref(x_62);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_68, 0, x_62);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_69, 0, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_65);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_72, 0, x_64);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_73, 0, x_63);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_66);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_71);
lean_ctor_set(x_33, 1, x_67);
lean_ctor_set(x_33, 0, x_74);
x_75 = l_ReaderT_instMonad___redArg(x_33);
x_76 = l_ReaderT_instMonad___redArg(x_75);
x_77 = l_ReaderT_instMonad___redArg(x_76);
x_78 = l_ReaderT_instMonad___redArg(x_77);
x_79 = l_ReaderT_instMonad___redArg(x_78);
x_80 = l_ReaderT_instMonad___redArg(x_79);
x_81 = l_ReaderT_instMonad___redArg(x_80);
x_82 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_83 = l_instInhabitedOfMonad___redArg(x_81, x_82);
x_84 = lean_panic_fn(x_83, x_1);
x_85 = lean_apply_12(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_86 = lean_ctor_get(x_33, 0);
lean_inc(x_86);
lean_dec(x_33);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_86, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 4);
lean_inc(x_90);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
 x_91 = lean_box(0);
}
x_92 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
x_93 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_inc_ref(x_87);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_94, 0, x_87);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_87);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_90);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_98, 0, x_89);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_99, 0, x_88);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_98);
lean_ctor_set(x_100, 4, x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_93);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l_ReaderT_instMonad___redArg(x_105);
x_107 = l_ReaderT_instMonad___redArg(x_106);
x_108 = l_ReaderT_instMonad___redArg(x_107);
x_109 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_110 = l_instInhabitedOfMonad___redArg(x_108, x_109);
x_111 = lean_panic_fn(x_110, x_1);
x_112 = lean_apply_12(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_113 = lean_ctor_get(x_17, 0);
x_114 = lean_ctor_get(x_17, 2);
x_115 = lean_ctor_get(x_17, 3);
x_116 = lean_ctor_get(x_17, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_17);
x_117 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1;
x_118 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2;
lean_inc_ref(x_113);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_119, 0, x_113);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_120, 0, x_113);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_122, 0, x_116);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_123, 0, x_115);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_124, 0, x_114);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_123);
lean_ctor_set(x_125, 4, x_122);
lean_ctor_set(x_15, 1, x_118);
lean_ctor_set(x_15, 0, x_125);
x_126 = l_ReaderT_instMonad___redArg(x_15);
x_127 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_127, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 4);
lean_inc(x_132);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 x_133 = x_127;
} else {
 lean_dec_ref(x_127);
 x_133 = lean_box(0);
}
x_134 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
x_135 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_inc_ref(x_129);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_137, 0, x_129);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_139, 0, x_132);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_140, 0, x_131);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_141, 0, x_130);
if (lean_is_scalar(x_133)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_133;
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_142, 3, x_140);
lean_ctor_set(x_142, 4, x_139);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_135);
x_144 = l_ReaderT_instMonad___redArg(x_143);
x_145 = l_ReaderT_instMonad___redArg(x_144);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = l_ReaderT_instMonad___redArg(x_146);
x_148 = l_ReaderT_instMonad___redArg(x_147);
x_149 = l_ReaderT_instMonad___redArg(x_148);
x_150 = l_ReaderT_instMonad___redArg(x_149);
x_151 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_152 = l_instInhabitedOfMonad___redArg(x_150, x_151);
x_153 = lean_panic_fn(x_152, x_1);
x_154 = lean_apply_12(x_153, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_155 = lean_ctor_get(x_15, 0);
lean_inc(x_155);
lean_dec(x_15);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_155, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 4);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
x_161 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1;
x_162 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2;
lean_inc_ref(x_156);
x_163 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_163, 0, x_156);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_164, 0, x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_159);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_167, 0, x_158);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_168, 0, x_157);
if (lean_is_scalar(x_160)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_160;
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_168);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set(x_169, 4, x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_162);
x_171 = l_ReaderT_instMonad___redArg(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_172, 0);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_172, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 3);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 4);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3;
x_180 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4;
lean_inc_ref(x_174);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_181, 0, x_174);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_182, 0, x_174);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_184, 0, x_177);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_185, 0, x_176);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_186, 0, x_175);
if (lean_is_scalar(x_178)) {
 x_187 = lean_alloc_ctor(0, 5, 0);
} else {
 x_187 = x_178;
}
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_186);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set(x_187, 4, x_184);
if (lean_is_scalar(x_173)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_173;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
x_189 = l_ReaderT_instMonad___redArg(x_188);
x_190 = l_ReaderT_instMonad___redArg(x_189);
x_191 = l_ReaderT_instMonad___redArg(x_190);
x_192 = l_ReaderT_instMonad___redArg(x_191);
x_193 = l_ReaderT_instMonad___redArg(x_192);
x_194 = l_ReaderT_instMonad___redArg(x_193);
x_195 = l_ReaderT_instMonad___redArg(x_194);
x_196 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_197 = l_instInhabitedOfMonad___redArg(x_195, x_196);
x_198 = lean_panic_fn(x_197, x_1);
x_199 = lean_apply_12(x_198, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_199;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skipping ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind linarith` internal cases, cases stack is empty", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_95; uint8_t x_96; 
x_77 = lean_st_ref_get(x_5);
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
lean_dec_ref(x_78);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_79);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5;
x_98 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_97, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_80 = x_5;
x_81 = x_12;
x_82 = x_13;
x_83 = x_14;
x_84 = x_15;
x_85 = lean_box(0);
goto block_94;
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec_ref(x_4);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
x_80 = x_5;
x_81 = x_12;
x_82 = x_13;
x_83 = x_14;
x_84 = x_15;
x_85 = lean_box(0);
goto block_94;
}
block_76:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_st_ref_take(x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_PersistentArray_pop___redArg(x_26);
lean_ctor_set(x_24, 0, x_27);
x_28 = lean_st_ref_set(x_17, x_24);
x_29 = lean_ctor_get(x_23, 1);
x_30 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_29, x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_29);
lean_dec_ref(x_23);
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
x_32 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_31, x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_29);
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3;
x_37 = l_Lean_MessageData_ofName(x_29);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_31, x_38, x_19, x_18, x_21, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
goto _start;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_4);
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
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec_ref(x_4);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_4);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_23);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = l_Lean_PersistentArray_pop___redArg(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_st_ref_set(x_17, x_53);
x_55 = lean_ctor_get(x_23, 1);
x_56 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_55, x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_55);
lean_dec_ref(x_23);
x_57 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
x_58 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_57, x_21);
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
lean_dec(x_55);
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3;
x_63 = l_Lean_MessageData_ofName(x_55);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_57, x_64, x_19, x_18, x_21, x_20);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_4);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_55);
lean_dec_ref(x_4);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_71 = x_58;
} else {
 lean_dec_ref(x_58);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_4);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_23);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
block_94:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_st_ref_get(x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_87, 2);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_79, x_89);
lean_dec(x_79);
x_91 = lean_nat_dec_lt(x_90, x_88);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec_ref(x_87);
lean_inc_ref(x_4);
x_92 = l_outOfBounds___redArg(x_4);
x_17 = x_80;
x_18 = x_82;
x_19 = x_81;
x_20 = x_84;
x_21 = x_83;
x_22 = lean_box(0);
x_23 = x_92;
goto block_76;
}
else
{
lean_object* x_93; 
lean_inc_ref(x_4);
x_93 = l_Lean_PersistentArray_get_x21___redArg(x_4, x_87, x_90);
lean_dec(x_90);
x_17 = x_80;
x_18 = x_82;
x_19 = x_81;
x_20 = x_84;
x_21 = x_83;
x_22 = lean_box(0);
x_23 = x_93;
goto block_76;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_95; uint8_t x_96; 
x_77 = lean_st_ref_get(x_5);
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
lean_dec_ref(x_78);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_79);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5;
x_98 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_97, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_80 = x_5;
x_81 = x_12;
x_82 = x_13;
x_83 = x_14;
x_84 = x_15;
x_85 = lean_box(0);
goto block_94;
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec_ref(x_4);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
x_80 = x_5;
x_81 = x_12;
x_82 = x_13;
x_83 = x_14;
x_84 = x_15;
x_85 = lean_box(0);
goto block_94;
}
block_76:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_st_ref_take(x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_PersistentArray_pop___redArg(x_26);
lean_ctor_set(x_24, 0, x_27);
x_28 = lean_st_ref_set(x_20, x_24);
x_29 = lean_ctor_get(x_23, 1);
x_30 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_29, x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_29);
lean_dec_ref(x_23);
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
x_32 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_31, x_17);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_29);
x_35 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3;
x_37 = l_Lean_MessageData_ofName(x_29);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_31, x_38, x_19, x_18, x_17, x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec_ref(x_39);
x_40 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_4);
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
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec_ref(x_4);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_4);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_23);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = l_Lean_PersistentArray_pop___redArg(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_st_ref_set(x_20, x_53);
x_55 = lean_ctor_get(x_23, 1);
x_56 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_55, x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_55);
lean_dec_ref(x_23);
x_57 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
x_58 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_57, x_17);
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
lean_object* x_61; 
lean_dec(x_55);
x_61 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3;
x_63 = l_Lean_MessageData_ofName(x_55);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_57, x_64, x_19, x_18, x_17, x_21);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec_ref(x_65);
x_66 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_4);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_55);
lean_dec_ref(x_4);
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_71 = x_58;
} else {
 lean_dec_ref(x_58);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_4);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_23);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
block_94:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_st_ref_get(x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_87, 2);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_79, x_89);
lean_dec(x_79);
x_91 = lean_nat_dec_lt(x_90, x_88);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec_ref(x_87);
lean_inc_ref(x_4);
x_92 = l_outOfBounds___redArg(x_4);
x_17 = x_83;
x_18 = x_82;
x_19 = x_81;
x_20 = x_80;
x_21 = x_84;
x_22 = lean_box(0);
x_23 = x_92;
goto block_76;
}
else
{
lean_object* x_93; 
lean_inc_ref(x_4);
x_93 = l_Lean_PersistentArray_get_x21___redArg(x_4, x_87, x_90);
lean_dec(x_90);
x_17 = x_83;
x_18 = x_82;
x_19 = x_81;
x_20 = x_80;
x_21 = x_84;
x_22 = lean_box(0);
x_23 = x_93;
goto block_76;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0() {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Linear.Search", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.Linear.Search.0.Lean.Meta.Grind.Arith.Linear.findCase", 91, 91);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(225u);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_15 = lean_box(0);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0;
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_16, x_15, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_17);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4;
x_22 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4;
x_27 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_27; 
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___redArg(x_1, x_2, x_12, x_13, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2___boxed(lean_object** _args) {
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
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
lean_object* x_27; 
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_2);
x_24 = lean_box(0);
x_25 = lean_array_fset(x_4, x_1, x_24);
x_26 = lean_array_fset(x_25, x_1, x_23);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_2);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_4, x_1, x_28);
x_30 = lean_array_fset(x_29, x_1, x_27);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_6);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set(x_31, 4, x_8);
lean_ctor_set(x_31, 5, x_9);
lean_ctor_set(x_31, 6, x_10);
lean_ctor_set(x_31, 7, x_11);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
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
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_8) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_5);
x_10 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_20 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_21 = lean_nat_add(x_20, x_12);
lean_dec(x_20);
if (lean_is_scalar(x_7)) {
 x_22 = lean_alloc_ctor(0, 5, 0);
} else {
 x_22 = x_7;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_23 = x_6;
} else {
 lean_dec_ref(x_6);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
x_26 = lean_ctor_get(x_15, 2);
x_27 = lean_ctor_get(x_15, 3);
x_28 = lean_ctor_get(x_15, 4);
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_mul(x_30, x_29);
x_32 = lean_nat_dec_lt(x_24, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_43; 
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 x_33 = x_15;
} else {
 lean_dec_ref(x_15);
 x_33 = lean_box(0);
}
x_34 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_35 = lean_nat_add(x_34, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
x_43 = x_50;
goto block_49;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_43 = x_51;
goto block_49;
}
block_42:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 5, 0);
} else {
 x_40 = x_33;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_13);
lean_ctor_set(x_40, 2, x_14);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_16);
if (lean_is_scalar(x_23)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_23;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_40);
return x_41;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_nat_add(x_34, x_43);
lean_dec(x_43);
lean_dec(x_34);
if (lean_is_scalar(x_7)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_7;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_9);
lean_ctor_set(x_45, 4, x_27);
x_46 = lean_nat_add(x_10, x_29);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
x_36 = x_45;
x_37 = x_46;
x_38 = x_47;
goto block_42;
}
else
{
lean_object* x_48; 
x_48 = lean_unsigned_to_nat(0u);
x_36 = x_45;
x_37 = x_46;
x_38 = x_48;
goto block_42;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_7);
x_52 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_53 = lean_nat_add(x_52, x_12);
lean_dec(x_12);
x_54 = lean_nat_add(x_52, x_24);
lean_dec(x_52);
lean_inc_ref(x_9);
if (lean_is_scalar(x_23)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_23;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_9);
lean_ctor_set(x_55, 4, x_15);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_9, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_9, 0);
lean_dec(x_61);
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 3, x_55);
lean_ctor_set(x_9, 2, x_14);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
else
{
lean_object* x_62; 
lean_dec(x_9);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_13);
lean_ctor_set(x_62, 2, x_14);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_16);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_9, 0);
lean_inc(x_63);
x_64 = lean_nat_add(x_10, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_7)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_7;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set(x_65, 3, x_9);
lean_ctor_set(x_65, 4, x_6);
return x_65;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_6, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_6, 4);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
x_71 = lean_ctor_get(x_6, 2);
x_72 = lean_ctor_get(x_6, 4);
lean_dec(x_72);
x_73 = lean_ctor_get(x_6, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_nat_add(x_10, x_69);
lean_dec(x_69);
x_76 = lean_nat_add(x_10, x_74);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 3, x_9);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_76);
if (lean_is_scalar(x_7)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_7;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_6);
lean_ctor_set(x_77, 4, x_67);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_6, 0);
x_79 = lean_ctor_get(x_6, 1);
x_80 = lean_ctor_get(x_6, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_6);
x_81 = lean_ctor_get(x_66, 0);
x_82 = lean_nat_add(x_10, x_78);
lean_dec(x_78);
x_83 = lean_nat_add(x_10, x_81);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_9);
lean_ctor_set(x_84, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_67);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_6, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_6, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_66);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_66, 1);
x_92 = lean_ctor_get(x_66, 2);
x_93 = lean_ctor_get(x_66, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_66, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_66, 0);
lean_dec(x_95);
x_96 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_66, 4, x_67);
lean_ctor_set(x_66, 3, x_67);
lean_ctor_set(x_66, 2, x_4);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_7;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set(x_97, 3, x_66);
lean_ctor_set(x_97, 4, x_6);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_66, 1);
x_99 = lean_ctor_get(x_66, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_66);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 2, x_4);
lean_ctor_set(x_101, 3, x_67);
lean_ctor_set(x_101, 4, x_67);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_7;
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_6);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_6);
x_105 = lean_ctor_get(x_66, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_66, 2);
lean_inc(x_106);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_107 = x_66;
} else {
 lean_dec_ref(x_66);
 x_107 = lean_box(0);
}
x_108 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_10);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 2, x_4);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_67);
lean_ctor_set(x_110, 4, x_67);
if (lean_is_scalar(x_7)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_7;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_106);
lean_ctor_set(x_111, 3, x_109);
lean_ctor_set(x_111, 4, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_6, 4);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_6);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_6, 1);
x_115 = lean_ctor_get(x_6, 2);
x_116 = lean_ctor_get(x_6, 4);
lean_dec(x_116);
x_117 = lean_ctor_get(x_6, 3);
lean_dec(x_117);
x_118 = lean_ctor_get(x_6, 0);
lean_dec(x_118);
x_119 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_7;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_6);
lean_ctor_set(x_120, 4, x_112);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get(x_6, 2);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_6);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_10);
lean_ctor_set(x_124, 1, x_3);
lean_ctor_set(x_124, 2, x_4);
lean_ctor_set(x_124, 3, x_66);
lean_ctor_set(x_124, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 5, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_122);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_112);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_6);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_6, 4);
lean_dec(x_127);
x_128 = lean_ctor_get(x_6, 3);
lean_dec(x_128);
lean_ctor_set(x_6, 3, x_112);
x_129 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_7;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 2, x_4);
lean_ctor_set(x_130, 3, x_112);
lean_ctor_set(x_130, 4, x_6);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_6, 0);
x_132 = lean_ctor_get(x_6, 1);
x_133 = lean_ctor_get(x_6, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_6);
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_112);
lean_ctor_set(x_134, 4, x_112);
x_135 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_7;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_4);
lean_ctor_set(x_136, 3, x_112);
lean_ctor_set(x_136, 4, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; 
if (lean_is_scalar(x_7)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_7;
}
lean_ctor_set(x_137, 0, x_10);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_6);
lean_ctor_set(x_137, 4, x_6);
return x_137;
}
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 2);
x_141 = lean_ctor_get(x_5, 3);
x_142 = lean_ctor_get(x_5, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_6, 0);
x_144 = lean_ctor_get(x_6, 1);
x_145 = lean_ctor_get(x_6, 2);
x_146 = lean_ctor_get(x_6, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_6, 4);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_nat_dec_lt(x_138, x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_150 = x_5;
} else {
 lean_dec_ref(x_5);
 x_150 = lean_box(0);
}
x_151 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_139, x_140, x_141, x_142);
x_152 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec_ref(x_151);
x_155 = lean_ctor_get(x_152, 0);
x_156 = lean_unsigned_to_nat(3u);
x_157 = lean_nat_mul(x_156, x_155);
x_158 = lean_nat_dec_lt(x_157, x_143);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_146);
x_159 = lean_nat_add(x_148, x_155);
x_160 = lean_nat_add(x_159, x_143);
lean_dec(x_159);
if (lean_is_scalar(x_150)) {
 x_161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_161 = x_150;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_152);
lean_ctor_set(x_161, 4, x_6);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_162 = x_6;
} else {
 lean_dec_ref(x_6);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_146, 0);
x_164 = lean_ctor_get(x_146, 1);
x_165 = lean_ctor_get(x_146, 2);
x_166 = lean_ctor_get(x_146, 3);
x_167 = lean_ctor_get(x_146, 4);
x_168 = lean_ctor_get(x_147, 0);
x_169 = lean_unsigned_to_nat(2u);
x_170 = lean_nat_mul(x_169, x_168);
x_171 = lean_nat_dec_lt(x_163, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_182; 
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_172 = x_146;
} else {
 lean_dec_ref(x_146);
 x_172 = lean_box(0);
}
x_173 = lean_nat_add(x_148, x_155);
x_174 = lean_nat_add(x_173, x_143);
lean_dec(x_143);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_166, 0);
lean_inc(x_189);
x_182 = x_189;
goto block_188;
}
else
{
lean_object* x_190; 
x_190 = lean_unsigned_to_nat(0u);
x_182 = x_190;
goto block_188;
}
block_181:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_nat_add(x_175, x_177);
lean_dec(x_177);
lean_dec(x_175);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(0, 5, 0);
} else {
 x_179 = x_172;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_144);
lean_ctor_set(x_179, 2, x_145);
lean_ctor_set(x_179, 3, x_167);
lean_ctor_set(x_179, 4, x_147);
if (lean_is_scalar(x_162)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_162;
}
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_164);
lean_ctor_set(x_180, 2, x_165);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_179);
return x_180;
}
block_188:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_nat_add(x_173, x_182);
lean_dec(x_182);
lean_dec(x_173);
if (lean_is_scalar(x_150)) {
 x_184 = lean_alloc_ctor(0, 5, 0);
} else {
 x_184 = x_150;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_153);
lean_ctor_set(x_184, 2, x_154);
lean_ctor_set(x_184, 3, x_152);
lean_ctor_set(x_184, 4, x_166);
x_185 = lean_nat_add(x_148, x_168);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
x_175 = x_185;
x_176 = x_184;
x_177 = x_186;
goto block_181;
}
else
{
lean_object* x_187; 
x_187 = lean_unsigned_to_nat(0u);
x_175 = x_185;
x_176 = x_184;
x_177 = x_187;
goto block_181;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_nat_add(x_148, x_155);
x_192 = lean_nat_add(x_191, x_143);
lean_dec(x_143);
x_193 = lean_nat_add(x_191, x_163);
lean_dec(x_191);
if (lean_is_scalar(x_162)) {
 x_194 = lean_alloc_ctor(0, 5, 0);
} else {
 x_194 = x_162;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_153);
lean_ctor_set(x_194, 2, x_154);
lean_ctor_set(x_194, 3, x_152);
lean_ctor_set(x_194, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_150;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_144);
lean_ctor_set(x_195, 2, x_145);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_147);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
x_196 = !lean_is_exclusive(x_6);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_6, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_6, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_6, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_6, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_6, 0);
lean_dec(x_201);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_151, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_151, 1);
lean_inc(x_203);
lean_dec_ref(x_151);
x_204 = lean_ctor_get(x_146, 0);
x_205 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_206 = lean_nat_add(x_148, x_204);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 3, x_152);
lean_ctor_set(x_6, 2, x_203);
lean_ctor_set(x_6, 1, x_202);
lean_ctor_set(x_6, 0, x_206);
if (lean_is_scalar(x_150)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_150;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_144);
lean_ctor_set(x_207, 2, x_145);
lean_ctor_set(x_207, 3, x_6);
lean_ctor_set(x_207, 4, x_147);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_143);
x_208 = lean_ctor_get(x_151, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_151, 1);
lean_inc(x_209);
lean_dec_ref(x_151);
x_210 = !lean_is_exclusive(x_146);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_146, 1);
x_212 = lean_ctor_get(x_146, 2);
x_213 = lean_ctor_get(x_146, 4);
lean_dec(x_213);
x_214 = lean_ctor_get(x_146, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_146, 0);
lean_dec(x_215);
x_216 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_146, 4, x_147);
lean_ctor_set(x_146, 3, x_147);
lean_ctor_set(x_146, 2, x_209);
lean_ctor_set(x_146, 1, x_208);
lean_ctor_set(x_146, 0, x_148);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_150;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set(x_217, 2, x_212);
lean_ctor_set(x_217, 3, x_146);
lean_ctor_set(x_217, 4, x_6);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_146, 1);
x_219 = lean_ctor_get(x_146, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_146);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_148);
lean_ctor_set(x_221, 1, x_208);
lean_ctor_set(x_221, 2, x_209);
lean_ctor_set(x_221, 3, x_147);
lean_ctor_set(x_221, 4, x_147);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_150;
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_6);
return x_222;
}
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_143);
x_223 = lean_ctor_get(x_151, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_151, 1);
lean_inc(x_224);
lean_dec_ref(x_151);
x_225 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 2, x_224);
lean_ctor_set(x_6, 1, x_223);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_150;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_144);
lean_ctor_set(x_226, 2, x_145);
lean_ctor_set(x_226, 3, x_6);
lean_ctor_set(x_226, 4, x_147);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_151, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_151, 1);
lean_inc(x_228);
lean_dec_ref(x_151);
lean_ctor_set(x_6, 3, x_147);
x_229 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_150;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_147);
lean_ctor_set(x_230, 4, x_6);
return x_230;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_151, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_151, 1);
lean_inc(x_232);
lean_dec_ref(x_151);
x_233 = lean_ctor_get(x_146, 0);
x_234 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_235 = lean_nat_add(x_148, x_233);
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_231);
lean_ctor_set(x_236, 2, x_232);
lean_ctor_set(x_236, 3, x_152);
lean_ctor_set(x_236, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_237 = lean_alloc_ctor(0, 5, 0);
} else {
 x_237 = x_150;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_144);
lean_ctor_set(x_237, 2, x_145);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_237, 4, x_147);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_143);
x_238 = lean_ctor_get(x_151, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_151, 1);
lean_inc(x_239);
lean_dec_ref(x_151);
x_240 = lean_ctor_get(x_146, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_146, 2);
lean_inc(x_241);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_242 = x_146;
} else {
 lean_dec_ref(x_146);
 x_242 = lean_box(0);
}
x_243 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_148);
lean_ctor_set(x_244, 1, x_238);
lean_ctor_set(x_244, 2, x_239);
lean_ctor_set(x_244, 3, x_147);
lean_ctor_set(x_244, 4, x_147);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_148);
lean_ctor_set(x_245, 1, x_144);
lean_ctor_set(x_245, 2, x_145);
lean_ctor_set(x_245, 3, x_147);
lean_ctor_set(x_245, 4, x_147);
if (lean_is_scalar(x_150)) {
 x_246 = lean_alloc_ctor(0, 5, 0);
} else {
 x_246 = x_150;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set(x_246, 4, x_245);
return x_246;
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_143);
x_247 = lean_ctor_get(x_151, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_151, 1);
lean_inc(x_248);
lean_dec_ref(x_151);
x_249 = lean_unsigned_to_nat(3u);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_148);
lean_ctor_set(x_250, 1, x_247);
lean_ctor_set(x_250, 2, x_248);
lean_ctor_set(x_250, 3, x_146);
lean_ctor_set(x_250, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_150;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_144);
lean_ctor_set(x_251, 2, x_145);
lean_ctor_set(x_251, 3, x_250);
lean_ctor_set(x_251, 4, x_147);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_151, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_151, 1);
lean_inc(x_253);
lean_dec_ref(x_151);
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_143);
lean_ctor_set(x_254, 1, x_144);
lean_ctor_set(x_254, 2, x_145);
lean_ctor_set(x_254, 3, x_147);
lean_ctor_set(x_254, 4, x_147);
x_255 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_256 = lean_alloc_ctor(0, 5, 0);
} else {
 x_256 = x_150;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_147);
lean_ctor_set(x_256, 4, x_254);
return x_256;
}
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_257 = x_6;
} else {
 lean_dec_ref(x_6);
 x_257 = lean_box(0);
}
x_258 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_144, x_145, x_146, x_147);
x_259 = lean_ctor_get(x_258, 2);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec_ref(x_258);
x_262 = lean_ctor_get(x_259, 0);
x_263 = lean_unsigned_to_nat(3u);
x_264 = lean_nat_mul(x_263, x_262);
x_265 = lean_nat_dec_lt(x_264, x_138);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_142);
x_266 = lean_nat_add(x_148, x_138);
x_267 = lean_nat_add(x_266, x_262);
lean_dec(x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_261);
lean_ctor_set(x_268, 3, x_5);
lean_ctor_set(x_268, 4, x_259);
return x_268;
}
else
{
uint8_t x_269; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_269 = !lean_is_exclusive(x_5);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_270 = lean_ctor_get(x_5, 4);
lean_dec(x_270);
x_271 = lean_ctor_get(x_5, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_5, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_5, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_5, 0);
lean_dec(x_274);
x_275 = lean_ctor_get(x_141, 0);
x_276 = lean_ctor_get(x_142, 0);
x_277 = lean_ctor_get(x_142, 1);
x_278 = lean_ctor_get(x_142, 2);
x_279 = lean_ctor_get(x_142, 3);
x_280 = lean_ctor_get(x_142, 4);
x_281 = lean_unsigned_to_nat(2u);
x_282 = lean_nat_mul(x_281, x_275);
x_283 = lean_nat_dec_lt(x_276, x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_300; lean_object* x_301; 
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_free_object(x_5);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_284 = x_142;
} else {
 lean_dec_ref(x_142);
 x_284 = lean_box(0);
}
x_285 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_286 = lean_nat_add(x_285, x_262);
lean_dec(x_285);
x_300 = lean_nat_add(x_148, x_275);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_279, 0);
lean_inc(x_308);
x_301 = x_308;
goto block_307;
}
else
{
lean_object* x_309; 
x_309 = lean_unsigned_to_nat(0u);
x_301 = x_309;
goto block_307;
}
block_299:
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_nat_add(x_288, x_289);
lean_dec(x_289);
lean_dec(x_288);
lean_inc_ref(x_259);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_260);
lean_ctor_set(x_291, 2, x_261);
lean_ctor_set(x_291, 3, x_280);
lean_ctor_set(x_291, 4, x_259);
x_292 = !lean_is_exclusive(x_259);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_259, 4);
lean_dec(x_293);
x_294 = lean_ctor_get(x_259, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_259, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_259, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_259, 0);
lean_dec(x_297);
lean_ctor_set(x_259, 4, x_291);
lean_ctor_set(x_259, 3, x_287);
lean_ctor_set(x_259, 2, x_278);
lean_ctor_set(x_259, 1, x_277);
lean_ctor_set(x_259, 0, x_286);
return x_259;
}
else
{
lean_object* x_298; 
lean_dec(x_259);
x_298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_298, 0, x_286);
lean_ctor_set(x_298, 1, x_277);
lean_ctor_set(x_298, 2, x_278);
lean_ctor_set(x_298, 3, x_287);
lean_ctor_set(x_298, 4, x_291);
return x_298;
}
}
block_307:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_nat_add(x_300, x_301);
lean_dec(x_301);
lean_dec(x_300);
if (lean_is_scalar(x_257)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_257;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_139);
lean_ctor_set(x_303, 2, x_140);
lean_ctor_set(x_303, 3, x_141);
lean_ctor_set(x_303, 4, x_279);
x_304 = lean_nat_add(x_148, x_262);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
x_287 = x_303;
x_288 = x_304;
x_289 = x_305;
goto block_299;
}
else
{
lean_object* x_306; 
x_306 = lean_unsigned_to_nat(0u);
x_287 = x_303;
x_288 = x_304;
x_289 = x_306;
goto block_299;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_310 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_311 = lean_nat_add(x_310, x_262);
lean_dec(x_310);
x_312 = lean_nat_add(x_148, x_262);
x_313 = lean_nat_add(x_312, x_276);
lean_dec(x_312);
if (lean_is_scalar(x_257)) {
 x_314 = lean_alloc_ctor(0, 5, 0);
} else {
 x_314 = x_257;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_260);
lean_ctor_set(x_314, 2, x_261);
lean_ctor_set(x_314, 3, x_142);
lean_ctor_set(x_314, 4, x_259);
lean_ctor_set(x_5, 4, x_314);
lean_ctor_set(x_5, 0, x_311);
return x_5;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_5);
x_315 = lean_ctor_get(x_141, 0);
x_316 = lean_ctor_get(x_142, 0);
x_317 = lean_ctor_get(x_142, 1);
x_318 = lean_ctor_get(x_142, 2);
x_319 = lean_ctor_get(x_142, 3);
x_320 = lean_ctor_get(x_142, 4);
x_321 = lean_unsigned_to_nat(2u);
x_322 = lean_nat_mul(x_321, x_315);
x_323 = lean_nat_dec_lt(x_316, x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_335; lean_object* x_336; 
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_324 = x_142;
} else {
 lean_dec_ref(x_142);
 x_324 = lean_box(0);
}
x_325 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_326 = lean_nat_add(x_325, x_262);
lean_dec(x_325);
x_335 = lean_nat_add(x_148, x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_319, 0);
lean_inc(x_343);
x_336 = x_343;
goto block_342;
}
else
{
lean_object* x_344; 
x_344 = lean_unsigned_to_nat(0u);
x_336 = x_344;
goto block_342;
}
block_334:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_nat_add(x_328, x_329);
lean_dec(x_329);
lean_dec(x_328);
lean_inc_ref(x_259);
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_324;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_260);
lean_ctor_set(x_331, 2, x_261);
lean_ctor_set(x_331, 3, x_320);
lean_ctor_set(x_331, 4, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_332 = x_259;
} else {
 lean_dec_ref(x_259);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 5, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_326);
lean_ctor_set(x_333, 1, x_317);
lean_ctor_set(x_333, 2, x_318);
lean_ctor_set(x_333, 3, x_327);
lean_ctor_set(x_333, 4, x_331);
return x_333;
}
block_342:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_nat_add(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
if (lean_is_scalar(x_257)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_257;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_139);
lean_ctor_set(x_338, 2, x_140);
lean_ctor_set(x_338, 3, x_141);
lean_ctor_set(x_338, 4, x_319);
x_339 = lean_nat_add(x_148, x_262);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_320, 0);
lean_inc(x_340);
x_327 = x_338;
x_328 = x_339;
x_329 = x_340;
goto block_334;
}
else
{
lean_object* x_341; 
x_341 = lean_unsigned_to_nat(0u);
x_327 = x_338;
x_328 = x_339;
x_329 = x_341;
goto block_334;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_346 = lean_nat_add(x_345, x_262);
lean_dec(x_345);
x_347 = lean_nat_add(x_148, x_262);
x_348 = lean_nat_add(x_347, x_316);
lean_dec(x_347);
if (lean_is_scalar(x_257)) {
 x_349 = lean_alloc_ctor(0, 5, 0);
} else {
 x_349 = x_257;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_260);
lean_ctor_set(x_349, 2, x_261);
lean_ctor_set(x_349, 3, x_142);
lean_ctor_set(x_349, 4, x_259);
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_139);
lean_ctor_set(x_350, 2, x_140);
lean_ctor_set(x_350, 3, x_141);
lean_ctor_set(x_350, 4, x_349);
return x_350;
}
}
}
}
else
{
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_351; 
lean_inc_ref(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_351 = !lean_is_exclusive(x_5);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_5, 4);
lean_dec(x_352);
x_353 = lean_ctor_get(x_5, 3);
lean_dec(x_353);
x_354 = lean_ctor_get(x_5, 2);
lean_dec(x_354);
x_355 = lean_ctor_get(x_5, 1);
lean_dec(x_355);
x_356 = lean_ctor_get(x_5, 0);
lean_dec(x_356);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_258, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_258, 1);
lean_inc(x_358);
lean_dec_ref(x_258);
x_359 = lean_ctor_get(x_142, 0);
x_360 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_361 = lean_nat_add(x_148, x_359);
if (lean_is_scalar(x_257)) {
 x_362 = lean_alloc_ctor(0, 5, 0);
} else {
 x_362 = x_257;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_357);
lean_ctor_set(x_362, 2, x_358);
lean_ctor_set(x_362, 3, x_142);
lean_ctor_set(x_362, 4, x_259);
lean_ctor_set(x_5, 4, x_362);
lean_ctor_set(x_5, 0, x_360);
return x_5;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_138);
x_363 = lean_ctor_get(x_258, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_258, 1);
lean_inc(x_364);
lean_dec_ref(x_258);
x_365 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_366 = lean_alloc_ctor(0, 5, 0);
} else {
 x_366 = x_257;
}
lean_ctor_set(x_366, 0, x_148);
lean_ctor_set(x_366, 1, x_363);
lean_ctor_set(x_366, 2, x_364);
lean_ctor_set(x_366, 3, x_142);
lean_ctor_set(x_366, 4, x_142);
lean_ctor_set(x_5, 4, x_366);
lean_ctor_set(x_5, 0, x_365);
return x_5;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_367 = lean_ctor_get(x_258, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_258, 1);
lean_inc(x_368);
lean_dec_ref(x_258);
x_369 = lean_ctor_get(x_142, 0);
x_370 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_371 = lean_nat_add(x_148, x_369);
if (lean_is_scalar(x_257)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_257;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
lean_ctor_set(x_372, 2, x_368);
lean_ctor_set(x_372, 3, x_142);
lean_ctor_set(x_372, 4, x_259);
x_373 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_139);
lean_ctor_set(x_373, 2, x_140);
lean_ctor_set(x_373, 3, x_141);
lean_ctor_set(x_373, 4, x_372);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_138);
x_374 = lean_ctor_get(x_258, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_258, 1);
lean_inc(x_375);
lean_dec_ref(x_258);
x_376 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_377 = lean_alloc_ctor(0, 5, 0);
} else {
 x_377 = x_257;
}
lean_ctor_set(x_377, 0, x_148);
lean_ctor_set(x_377, 1, x_374);
lean_ctor_set(x_377, 2, x_375);
lean_ctor_set(x_377, 3, x_142);
lean_ctor_set(x_377, 4, x_142);
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_139);
lean_ctor_set(x_378, 2, x_140);
lean_ctor_set(x_378, 3, x_141);
lean_ctor_set(x_378, 4, x_377);
return x_378;
}
}
}
else
{
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_379; 
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
x_379 = !lean_is_exclusive(x_5);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_380 = lean_ctor_get(x_5, 4);
lean_dec(x_380);
x_381 = lean_ctor_get(x_5, 3);
lean_dec(x_381);
x_382 = lean_ctor_get(x_5, 2);
lean_dec(x_382);
x_383 = lean_ctor_get(x_5, 1);
lean_dec(x_383);
x_384 = lean_ctor_get(x_5, 0);
lean_dec(x_384);
x_385 = lean_ctor_get(x_258, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_258, 1);
lean_inc(x_386);
lean_dec_ref(x_258);
x_387 = !lean_is_exclusive(x_142);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_ctor_get(x_142, 1);
x_389 = lean_ctor_get(x_142, 2);
x_390 = lean_ctor_get(x_142, 4);
lean_dec(x_390);
x_391 = lean_ctor_get(x_142, 3);
lean_dec(x_391);
x_392 = lean_ctor_get(x_142, 0);
lean_dec(x_392);
x_393 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_142, 4, x_141);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set(x_142, 0, x_148);
if (lean_is_scalar(x_257)) {
 x_394 = lean_alloc_ctor(0, 5, 0);
} else {
 x_394 = x_257;
}
lean_ctor_set(x_394, 0, x_148);
lean_ctor_set(x_394, 1, x_385);
lean_ctor_set(x_394, 2, x_386);
lean_ctor_set(x_394, 3, x_141);
lean_ctor_set(x_394, 4, x_141);
lean_ctor_set(x_5, 4, x_394);
lean_ctor_set(x_5, 3, x_142);
lean_ctor_set(x_5, 2, x_389);
lean_ctor_set(x_5, 1, x_388);
lean_ctor_set(x_5, 0, x_393);
return x_5;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_395 = lean_ctor_get(x_142, 1);
x_396 = lean_ctor_get(x_142, 2);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_142);
x_397 = lean_unsigned_to_nat(3u);
x_398 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_398, 0, x_148);
lean_ctor_set(x_398, 1, x_139);
lean_ctor_set(x_398, 2, x_140);
lean_ctor_set(x_398, 3, x_141);
lean_ctor_set(x_398, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_399 = lean_alloc_ctor(0, 5, 0);
} else {
 x_399 = x_257;
}
lean_ctor_set(x_399, 0, x_148);
lean_ctor_set(x_399, 1, x_385);
lean_ctor_set(x_399, 2, x_386);
lean_ctor_set(x_399, 3, x_141);
lean_ctor_set(x_399, 4, x_141);
lean_ctor_set(x_5, 4, x_399);
lean_ctor_set(x_5, 3, x_398);
lean_ctor_set(x_5, 2, x_396);
lean_ctor_set(x_5, 1, x_395);
lean_ctor_set(x_5, 0, x_397);
return x_5;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_5);
x_400 = lean_ctor_get(x_258, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_258, 1);
lean_inc(x_401);
lean_dec_ref(x_258);
x_402 = lean_ctor_get(x_142, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_142, 2);
lean_inc(x_403);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_404 = x_142;
} else {
 lean_dec_ref(x_142);
 x_404 = lean_box(0);
}
x_405 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 5, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_148);
lean_ctor_set(x_406, 1, x_139);
lean_ctor_set(x_406, 2, x_140);
lean_ctor_set(x_406, 3, x_141);
lean_ctor_set(x_406, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_407 = lean_alloc_ctor(0, 5, 0);
} else {
 x_407 = x_257;
}
lean_ctor_set(x_407, 0, x_148);
lean_ctor_set(x_407, 1, x_400);
lean_ctor_set(x_407, 2, x_401);
lean_ctor_set(x_407, 3, x_141);
lean_ctor_set(x_407, 4, x_141);
x_408 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_402);
lean_ctor_set(x_408, 2, x_403);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set(x_408, 4, x_407);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_258, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_258, 1);
lean_inc(x_410);
lean_dec_ref(x_258);
x_411 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_257)) {
 x_412 = lean_alloc_ctor(0, 5, 0);
} else {
 x_412 = x_257;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_409);
lean_ctor_set(x_412, 2, x_410);
lean_ctor_set(x_412, 3, x_5);
lean_ctor_set(x_412, 4, x_142);
return x_412;
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_6);
x_414 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_413) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_5, 0);
x_417 = lean_ctor_get(x_5, 1);
x_418 = lean_ctor_get(x_5, 2);
x_419 = lean_ctor_get(x_5, 3);
x_420 = lean_ctor_get(x_5, 4);
lean_inc(x_420);
x_421 = lean_unsigned_to_nat(3u);
x_422 = lean_nat_mul(x_421, x_415);
x_423 = lean_nat_dec_lt(x_422, x_416);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
x_424 = lean_nat_add(x_414, x_416);
x_425 = lean_nat_add(x_424, x_415);
lean_dec(x_415);
lean_dec(x_424);
if (lean_is_scalar(x_7)) {
 x_426 = lean_alloc_ctor(0, 5, 0);
} else {
 x_426 = x_7;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_3);
lean_ctor_set(x_426, 2, x_4);
lean_ctor_set(x_426, 3, x_5);
lean_ctor_set(x_426, 4, x_413);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_427 = x_5;
} else {
 lean_dec_ref(x_5);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_419, 0);
x_429 = lean_ctor_get(x_420, 0);
x_430 = lean_ctor_get(x_420, 1);
x_431 = lean_ctor_get(x_420, 2);
x_432 = lean_ctor_get(x_420, 3);
x_433 = lean_ctor_get(x_420, 4);
x_434 = lean_unsigned_to_nat(2u);
x_435 = lean_nat_mul(x_434, x_428);
x_436 = lean_nat_dec_lt(x_429, x_435);
lean_dec(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_447; lean_object* x_448; 
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 x_437 = x_420;
} else {
 lean_dec_ref(x_420);
 x_437 = lean_box(0);
}
x_438 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_439 = lean_nat_add(x_438, x_415);
lean_dec(x_438);
x_447 = lean_nat_add(x_414, x_428);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_432, 0);
lean_inc(x_455);
x_448 = x_455;
goto block_454;
}
else
{
lean_object* x_456; 
x_456 = lean_unsigned_to_nat(0u);
x_448 = x_456;
goto block_454;
}
block_446:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_nat_add(x_441, x_442);
lean_dec(x_442);
lean_dec(x_441);
if (lean_is_scalar(x_437)) {
 x_444 = lean_alloc_ctor(0, 5, 0);
} else {
 x_444 = x_437;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_3);
lean_ctor_set(x_444, 2, x_4);
lean_ctor_set(x_444, 3, x_433);
lean_ctor_set(x_444, 4, x_413);
if (lean_is_scalar(x_427)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_427;
}
lean_ctor_set(x_445, 0, x_439);
lean_ctor_set(x_445, 1, x_430);
lean_ctor_set(x_445, 2, x_431);
lean_ctor_set(x_445, 3, x_440);
lean_ctor_set(x_445, 4, x_444);
return x_445;
}
block_454:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_nat_add(x_447, x_448);
lean_dec(x_448);
lean_dec(x_447);
if (lean_is_scalar(x_7)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_7;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_417);
lean_ctor_set(x_450, 2, x_418);
lean_ctor_set(x_450, 3, x_419);
lean_ctor_set(x_450, 4, x_432);
x_451 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_433, 0);
lean_inc(x_452);
x_440 = x_450;
x_441 = x_451;
x_442 = x_452;
goto block_446;
}
else
{
lean_object* x_453; 
x_453 = lean_unsigned_to_nat(0u);
x_440 = x_450;
x_441 = x_451;
x_442 = x_453;
goto block_446;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_7);
x_457 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_458 = lean_nat_add(x_457, x_415);
lean_dec(x_457);
x_459 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
x_460 = lean_nat_add(x_459, x_429);
lean_dec(x_459);
lean_inc_ref(x_413);
if (lean_is_scalar(x_427)) {
 x_461 = lean_alloc_ctor(0, 5, 0);
} else {
 x_461 = x_427;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_3);
lean_ctor_set(x_461, 2, x_4);
lean_ctor_set(x_461, 3, x_420);
lean_ctor_set(x_461, 4, x_413);
x_462 = !lean_is_exclusive(x_413);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_413, 4);
lean_dec(x_463);
x_464 = lean_ctor_get(x_413, 3);
lean_dec(x_464);
x_465 = lean_ctor_get(x_413, 2);
lean_dec(x_465);
x_466 = lean_ctor_get(x_413, 1);
lean_dec(x_466);
x_467 = lean_ctor_get(x_413, 0);
lean_dec(x_467);
lean_ctor_set(x_413, 4, x_461);
lean_ctor_set(x_413, 3, x_419);
lean_ctor_set(x_413, 2, x_418);
lean_ctor_set(x_413, 1, x_417);
lean_ctor_set(x_413, 0, x_458);
return x_413;
}
else
{
lean_object* x_468; 
lean_dec(x_413);
x_468 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_468, 0, x_458);
lean_ctor_set(x_468, 1, x_417);
lean_ctor_set(x_468, 2, x_418);
lean_ctor_set(x_468, 3, x_419);
lean_ctor_set(x_468, 4, x_461);
return x_468;
}
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_413, 0);
lean_inc(x_469);
x_470 = lean_nat_add(x_414, x_469);
lean_dec(x_469);
if (lean_is_scalar(x_7)) {
 x_471 = lean_alloc_ctor(0, 5, 0);
} else {
 x_471 = x_7;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_3);
lean_ctor_set(x_471, 2, x_4);
lean_ctor_set(x_471, 3, x_5);
lean_ctor_set(x_471, 4, x_413);
return x_471;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
lean_inc_ref(x_472);
x_473 = lean_ctor_get(x_5, 4);
lean_inc(x_473);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_5);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_475 = lean_ctor_get(x_5, 0);
x_476 = lean_ctor_get(x_5, 1);
x_477 = lean_ctor_get(x_5, 2);
x_478 = lean_ctor_get(x_5, 4);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 3);
lean_dec(x_479);
x_480 = lean_ctor_get(x_473, 0);
x_481 = lean_nat_add(x_414, x_475);
lean_dec(x_475);
x_482 = lean_nat_add(x_414, x_480);
lean_ctor_set(x_5, 4, x_413);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_482);
if (lean_is_scalar(x_7)) {
 x_483 = lean_alloc_ctor(0, 5, 0);
} else {
 x_483 = x_7;
}
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_472);
lean_ctor_set(x_483, 4, x_5);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = lean_ctor_get(x_5, 0);
x_485 = lean_ctor_get(x_5, 1);
x_486 = lean_ctor_get(x_5, 2);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_5);
x_487 = lean_ctor_get(x_473, 0);
x_488 = lean_nat_add(x_414, x_484);
lean_dec(x_484);
x_489 = lean_nat_add(x_414, x_487);
x_490 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
lean_ctor_set(x_490, 2, x_4);
lean_ctor_set(x_490, 3, x_473);
lean_ctor_set(x_490, 4, x_413);
if (lean_is_scalar(x_7)) {
 x_491 = lean_alloc_ctor(0, 5, 0);
} else {
 x_491 = x_7;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_485);
lean_ctor_set(x_491, 2, x_486);
lean_ctor_set(x_491, 3, x_472);
lean_ctor_set(x_491, 4, x_490);
return x_491;
}
}
else
{
uint8_t x_492; 
x_492 = !lean_is_exclusive(x_5);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_5, 1);
x_494 = lean_ctor_get(x_5, 2);
x_495 = lean_ctor_get(x_5, 4);
lean_dec(x_495);
x_496 = lean_ctor_get(x_5, 3);
lean_dec(x_496);
x_497 = lean_ctor_get(x_5, 0);
lean_dec(x_497);
x_498 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_499 = lean_alloc_ctor(0, 5, 0);
} else {
 x_499 = x_7;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_493);
lean_ctor_set(x_499, 2, x_494);
lean_ctor_set(x_499, 3, x_472);
lean_ctor_set(x_499, 4, x_5);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_ctor_get(x_5, 1);
x_501 = lean_ctor_get(x_5, 2);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_5);
x_502 = lean_unsigned_to_nat(3u);
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_414);
lean_ctor_set(x_503, 1, x_3);
lean_ctor_set(x_503, 2, x_4);
lean_ctor_set(x_503, 3, x_473);
lean_ctor_set(x_503, 4, x_473);
if (lean_is_scalar(x_7)) {
 x_504 = lean_alloc_ctor(0, 5, 0);
} else {
 x_504 = x_7;
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_500);
lean_ctor_set(x_504, 2, x_501);
lean_ctor_set(x_504, 3, x_472);
lean_ctor_set(x_504, 4, x_503);
return x_504;
}
}
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_5, 4);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
uint8_t x_506; 
lean_inc(x_472);
x_506 = !lean_is_exclusive(x_5);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_507 = lean_ctor_get(x_5, 1);
x_508 = lean_ctor_get(x_5, 2);
x_509 = lean_ctor_get(x_5, 4);
lean_dec(x_509);
x_510 = lean_ctor_get(x_5, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_5, 0);
lean_dec(x_511);
x_512 = !lean_is_exclusive(x_505);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_513 = lean_ctor_get(x_505, 1);
x_514 = lean_ctor_get(x_505, 2);
x_515 = lean_ctor_get(x_505, 4);
lean_dec(x_515);
x_516 = lean_ctor_get(x_505, 3);
lean_dec(x_516);
x_517 = lean_ctor_get(x_505, 0);
lean_dec(x_517);
x_518 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_505, 4, x_472);
lean_ctor_set(x_505, 3, x_472);
lean_ctor_set(x_505, 2, x_508);
lean_ctor_set(x_505, 1, x_507);
lean_ctor_set(x_505, 0, x_414);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_519 = lean_alloc_ctor(0, 5, 0);
} else {
 x_519 = x_7;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_513);
lean_ctor_set(x_519, 2, x_514);
lean_ctor_set(x_519, 3, x_505);
lean_ctor_set(x_519, 4, x_5);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_520 = lean_ctor_get(x_505, 1);
x_521 = lean_ctor_get(x_505, 2);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_505);
x_522 = lean_unsigned_to_nat(3u);
x_523 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_523, 0, x_414);
lean_ctor_set(x_523, 1, x_507);
lean_ctor_set(x_523, 2, x_508);
lean_ctor_set(x_523, 3, x_472);
lean_ctor_set(x_523, 4, x_472);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_7;
}
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_520);
lean_ctor_set(x_524, 2, x_521);
lean_ctor_set(x_524, 3, x_523);
lean_ctor_set(x_524, 4, x_5);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_525 = lean_ctor_get(x_5, 1);
x_526 = lean_ctor_get(x_5, 2);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_5);
x_527 = lean_ctor_get(x_505, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_505, 2);
lean_inc(x_528);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 lean_ctor_release(x_505, 4);
 x_529 = x_505;
} else {
 lean_dec_ref(x_505);
 x_529 = lean_box(0);
}
x_530 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_529)) {
 x_531 = lean_alloc_ctor(0, 5, 0);
} else {
 x_531 = x_529;
}
lean_ctor_set(x_531, 0, x_414);
lean_ctor_set(x_531, 1, x_525);
lean_ctor_set(x_531, 2, x_526);
lean_ctor_set(x_531, 3, x_472);
lean_ctor_set(x_531, 4, x_472);
x_532 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_532, 0, x_414);
lean_ctor_set(x_532, 1, x_3);
lean_ctor_set(x_532, 2, x_4);
lean_ctor_set(x_532, 3, x_472);
lean_ctor_set(x_532, 4, x_472);
if (lean_is_scalar(x_7)) {
 x_533 = lean_alloc_ctor(0, 5, 0);
} else {
 x_533 = x_7;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_527);
lean_ctor_set(x_533, 2, x_528);
lean_ctor_set(x_533, 3, x_531);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_535 = lean_alloc_ctor(0, 5, 0);
} else {
 x_535 = x_7;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_5);
lean_ctor_set(x_535, 4, x_505);
return x_535;
}
}
}
else
{
lean_object* x_536; 
if (lean_is_scalar(x_7)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_7;
}
lean_ctor_set(x_536, 0, x_414);
lean_ctor_set(x_536, 1, x_3);
lean_ctor_set(x_536, 2, x_4);
lean_ctor_set(x_536, 3, x_5);
lean_ctor_set(x_536, 4, x_5);
return x_536;
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_MessageData_ofName(x_5);
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
x_11 = l_Lean_MessageData_ofName(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 21);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
x_18 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 21);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1;
x_24 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 20);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_free_object(x_12);
x_17 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
x_18 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_17, x_7, x_8, x_9, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_19, 20);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1;
x_24 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_23, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_2 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 18);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = l_Lean_mkAppB(x_16, x_18, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 18);
lean_inc_ref(x_25);
lean_dec(x_24);
x_26 = l_Lean_mkAppB(x_16, x_18, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_dec(x_16);
return x_17;
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Grind_Linarith_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__2_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 18);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = l_Lean_mkAppB(x_32, x_34, x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_40, 18);
lean_inc_ref(x_41);
lean_dec(x_40);
x_42 = l_Lean_mkAppB(x_32, x_34, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_32);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_dec(x_32);
return x_33;
}
}
else
{
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_16 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resolved diseq split: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtracking ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dec vars: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resolve conflict, decision stack: ", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_14 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1;
x_160 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_14, x_11);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
x_118 = x_2;
x_119 = x_3;
x_120 = x_4;
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_10;
x_127 = x_11;
x_128 = x_12;
x_129 = lean_box(0);
goto block_159;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_st_ref_get(x_2);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
lean_dec(x_166);
x_167 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10;
x_168 = l_Lean_PersistentArray_toList___redArg(x_165);
lean_dec_ref(x_165);
x_169 = lean_box(0);
x_170 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(x_168, x_169);
x_171 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_170, x_169);
x_172 = l_Lean_MessageData_ofList(x_171);
lean_ctor_set_tag(x_163, 7);
lean_ctor_set(x_163, 1, x_172);
lean_ctor_set(x_163, 0, x_167);
x_173 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_163, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_173);
x_118 = x_2;
x_119 = x_3;
x_120 = x_4;
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_10;
x_127 = x_11;
x_128 = x_12;
x_129 = lean_box(0);
goto block_159;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_163, 0);
lean_inc(x_174);
lean_dec(x_163);
x_175 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10;
x_176 = l_Lean_PersistentArray_toList___redArg(x_174);
lean_dec_ref(x_174);
x_177 = lean_box(0);
x_178 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__6(x_176, x_177);
x_179 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_178, x_177);
x_180 = l_Lean_MessageData_ofList(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_181, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_182) == 0)
{
lean_dec_ref(x_182);
x_118 = x_2;
x_119 = x_3;
x_120 = x_4;
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_10;
x_127 = x_11;
x_128 = x_12;
x_129 = lean_box(0);
goto block_159;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_182;
}
}
}
block_53:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_14, x_20);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_30);
lean_dec(x_30);
x_35 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_34, x_16);
x_36 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0;
lean_inc(x_31);
x_37 = l_Lean_Grind_Linarith_Poly_mul(x_31, x_36);
x_38 = 1;
x_39 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_1);
lean_ctor_set(x_39, 3, x_35);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_38);
x_41 = lean_unbox(x_33);
lean_dec(x_33);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_27);
x_42 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_40, x_15, x_23, x_18, x_26, x_29, x_24, x_21, x_19, x_20, x_25);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2(x_40, x_27, x_15, x_23, x_18, x_26, x_29, x_24, x_21, x_19, x_20, x_25);
lean_dec(x_27);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1;
x_46 = l_Lean_MessageData_ofExpr(x_44);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_47, x_21, x_19, x_20, x_25);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_48);
x_49 = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_assert(x_40, x_15, x_23, x_18, x_26, x_29, x_24, x_21, x_19, x_20, x_25);
return x_49;
}
else
{
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
return x_48;
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
block_72:
{
lean_object* x_70; 
x_70 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_56, x_57);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
lean_dec(x_54);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_15 = x_59;
x_16 = x_70;
x_17 = x_56;
x_18 = x_61;
x_19 = x_66;
x_20 = x_67;
x_21 = x_65;
x_22 = x_55;
x_23 = x_60;
x_24 = x_64;
x_25 = x_68;
x_26 = x_62;
x_27 = x_58;
x_28 = lean_box(0);
x_29 = x_63;
x_30 = x_71;
goto block_53;
}
else
{
x_15 = x_59;
x_16 = x_70;
x_17 = x_56;
x_18 = x_61;
x_19 = x_66;
x_20 = x_67;
x_21 = x_65;
x_22 = x_55;
x_23 = x_60;
x_24 = x_64;
x_25 = x_68;
x_26 = x_62;
x_27 = x_58;
x_28 = lean_box(0);
x_29 = x_63;
x_30 = x_54;
goto block_53;
}
}
block_117:
{
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_87; 
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase(x_74, x_75, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
lean_inc(x_88);
lean_inc(x_76);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___lam__0___boxed), 3, 2);
lean_closure_set(x_89, 0, x_76);
lean_closure_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_91 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_90, x_89, x_77);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_91);
x_92 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_14, x_84);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
lean_dec(x_88);
x_54 = x_73;
x_55 = x_95;
x_56 = x_96;
x_57 = x_74;
x_58 = x_75;
x_59 = x_76;
x_60 = x_77;
x_61 = x_78;
x_62 = x_79;
x_63 = x_80;
x_64 = x_81;
x_65 = x_82;
x_66 = x_83;
x_67 = x_84;
x_68 = x_85;
x_69 = lean_box(0);
goto block_72;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_dec(x_88);
x_99 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3;
lean_inc(x_98);
x_100 = l_Lean_MessageData_ofName(x_98);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_101, x_82, x_83, x_84, x_85);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
x_54 = x_73;
x_55 = x_97;
x_56 = x_98;
x_57 = x_74;
x_58 = x_75;
x_59 = x_76;
x_60 = x_77;
x_61 = x_78;
x_62 = x_79;
x_63 = x_80;
x_64 = x_81;
x_65 = x_82;
x_66 = x_83;
x_67 = x_84;
x_68 = x_85;
x_69 = lean_box(0);
goto block_72;
}
else
{
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
return x_102;
}
}
}
else
{
lean_dec(x_88);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
return x_91;
}
}
else
{
uint8_t x_103; 
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_87);
if (x_103 == 0)
{
return x_87;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_87, 0);
lean_inc(x_104);
lean_dec(x_87);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_75);
lean_dec(x_73);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_106 = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_toExprProof(x_1, x_76, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_Lean_Meta_Grind_closeGoal(x_107, x_77, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
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
lean_object* x_112; lean_object* x_113; 
lean_dec(x_108);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
return x_108;
}
}
else
{
uint8_t x_114; 
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_106, 0);
lean_inc(x_115);
lean_dec(x_106);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
}
block_159:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_130 = lean_st_ref_get(x_118);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6;
lean_inc_ref(x_1);
x_134 = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_collectDecVars(x_1, x_131, x_133);
lean_dec(x_131);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_14, x_127);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_73 = x_132;
x_74 = x_139;
x_75 = x_118;
x_76 = x_119;
x_77 = x_120;
x_78 = x_121;
x_79 = x_122;
x_80 = x_123;
x_81 = x_124;
x_82 = x_125;
x_83 = x_126;
x_84 = x_127;
x_85 = x_128;
x_86 = lean_box(0);
goto block_117;
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_135, 1);
x_142 = lean_ctor_get(x_135, 0);
lean_dec(x_142);
x_143 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8;
x_144 = lean_box(0);
x_145 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_144, x_141);
x_146 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(x_145, x_144);
x_147 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_146, x_144);
x_148 = l_Lean_MessageData_ofList(x_147);
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_148);
lean_ctor_set(x_135, 0, x_143);
x_149 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_135, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_149) == 0)
{
lean_dec_ref(x_149);
x_73 = x_132;
x_74 = x_141;
x_75 = x_118;
x_76 = x_119;
x_77 = x_120;
x_78 = x_121;
x_79 = x_122;
x_80 = x_123;
x_81 = x_124;
x_82 = x_125;
x_83 = x_126;
x_84 = x_127;
x_85 = x_128;
x_86 = lean_box(0);
goto block_117;
}
else
{
lean_dec(x_141);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec_ref(x_1);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_150 = lean_ctor_get(x_135, 1);
lean_inc(x_150);
lean_dec(x_135);
x_151 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8;
x_152 = lean_box(0);
x_153 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__3(x_152, x_150);
x_154 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__4(x_153, x_152);
x_155 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__5(x_154, x_152);
x_156 = l_Lean_MessageData_ofList(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_14, x_157, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_158) == 0)
{
lean_dec_ref(x_158);
x_73 = x_132;
x_74 = x_150;
x_75 = x_118;
x_76 = x_119;
x_77 = x_120;
x_78 = x_121;
x_79 = x_122;
x_80 = x_123;
x_81 = x_124;
x_82 = x_125;
x_83 = x_126;
x_84 = x_127;
x_85 = x_128;
x_86 = lean_box(0);
goto block_117;
}
else
{
lean_dec(x_150);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec_ref(x_1);
return x_158;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resolveConflict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__1_spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_resolveConflict_spec__2_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 2);
x_27 = lean_ctor_get(x_23, 3);
x_28 = lean_ctor_get(x_23, 4);
x_29 = lean_ctor_get(x_23, 5);
x_30 = lean_ctor_get(x_23, 6);
x_31 = lean_ctor_get(x_23, 7);
x_32 = lean_ctor_get(x_23, 8);
x_33 = lean_ctor_get(x_23, 9);
x_34 = lean_ctor_get(x_23, 10);
x_35 = lean_ctor_get(x_23, 11);
x_36 = lean_ctor_get(x_23, 12);
x_37 = lean_ctor_get(x_23, 13);
x_38 = lean_ctor_get(x_23, 14);
x_39 = lean_ctor_get(x_23, 15);
x_40 = lean_ctor_get(x_23, 16);
x_41 = lean_ctor_get(x_23, 17);
x_42 = lean_ctor_get(x_23, 18);
x_43 = lean_ctor_get(x_23, 19);
x_44 = lean_ctor_get(x_23, 20);
x_45 = lean_ctor_get(x_23, 21);
x_46 = lean_ctor_get(x_23, 22);
x_47 = lean_ctor_get(x_23, 23);
x_48 = lean_ctor_get(x_23, 24);
x_49 = lean_ctor_get(x_23, 25);
x_50 = lean_ctor_get(x_23, 26);
x_51 = lean_ctor_get(x_23, 27);
x_52 = lean_ctor_get(x_23, 28);
x_53 = lean_ctor_get(x_23, 29);
x_54 = lean_ctor_get(x_23, 30);
x_55 = lean_ctor_get(x_23, 31);
x_56 = lean_ctor_get(x_23, 32);
x_57 = lean_ctor_get(x_23, 33);
x_58 = lean_ctor_get(x_23, 34);
x_59 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_60 = lean_ctor_get(x_23, 36);
x_61 = lean_ctor_get(x_23, 37);
x_62 = lean_ctor_get(x_23, 38);
x_63 = lean_ctor_get(x_23, 39);
x_64 = lean_ctor_get(x_23, 40);
x_65 = lean_ctor_get(x_23, 41);
x_66 = lean_array_fget(x_4, x_1);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_68 = lean_ctor_get(x_66, 41);
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 40);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 39);
lean_dec(x_70);
x_71 = lean_ctor_get(x_66, 38);
lean_dec(x_71);
x_72 = lean_ctor_get(x_66, 37);
lean_dec(x_72);
x_73 = lean_ctor_get(x_66, 36);
lean_dec(x_73);
x_74 = lean_ctor_get(x_66, 34);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 33);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 32);
lean_dec(x_76);
x_77 = lean_ctor_get(x_66, 31);
lean_dec(x_77);
x_78 = lean_ctor_get(x_66, 30);
lean_dec(x_78);
x_79 = lean_ctor_get(x_66, 29);
lean_dec(x_79);
x_80 = lean_ctor_get(x_66, 28);
lean_dec(x_80);
x_81 = lean_ctor_get(x_66, 27);
lean_dec(x_81);
x_82 = lean_ctor_get(x_66, 26);
lean_dec(x_82);
x_83 = lean_ctor_get(x_66, 25);
lean_dec(x_83);
x_84 = lean_ctor_get(x_66, 24);
lean_dec(x_84);
x_85 = lean_ctor_get(x_66, 23);
lean_dec(x_85);
x_86 = lean_ctor_get(x_66, 22);
lean_dec(x_86);
x_87 = lean_ctor_get(x_66, 21);
lean_dec(x_87);
x_88 = lean_ctor_get(x_66, 20);
lean_dec(x_88);
x_89 = lean_ctor_get(x_66, 19);
lean_dec(x_89);
x_90 = lean_ctor_get(x_66, 18);
lean_dec(x_90);
x_91 = lean_ctor_get(x_66, 17);
lean_dec(x_91);
x_92 = lean_ctor_get(x_66, 16);
lean_dec(x_92);
x_93 = lean_ctor_get(x_66, 15);
lean_dec(x_93);
x_94 = lean_ctor_get(x_66, 14);
lean_dec(x_94);
x_95 = lean_ctor_get(x_66, 13);
lean_dec(x_95);
x_96 = lean_ctor_get(x_66, 12);
lean_dec(x_96);
x_97 = lean_ctor_get(x_66, 11);
lean_dec(x_97);
x_98 = lean_ctor_get(x_66, 10);
lean_dec(x_98);
x_99 = lean_ctor_get(x_66, 9);
lean_dec(x_99);
x_100 = lean_ctor_get(x_66, 8);
lean_dec(x_100);
x_101 = lean_ctor_get(x_66, 7);
lean_dec(x_101);
x_102 = lean_ctor_get(x_66, 6);
lean_dec(x_102);
x_103 = lean_ctor_get(x_66, 5);
lean_dec(x_103);
x_104 = lean_ctor_get(x_66, 4);
lean_dec(x_104);
x_105 = lean_ctor_get(x_66, 3);
lean_dec(x_105);
x_106 = lean_ctor_get(x_66, 2);
lean_dec(x_106);
x_107 = lean_ctor_get(x_66, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_66, 0);
lean_dec(x_108);
x_109 = lean_box(0);
x_110 = lean_array_fset(x_4, x_1, x_109);
lean_inc_ref(x_65);
lean_inc_ref(x_64);
lean_inc(x_63);
lean_inc_ref(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_58);
lean_inc_ref(x_57);
lean_inc_ref(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_ctor_set(x_66, 41, x_65);
lean_ctor_set(x_66, 40, x_64);
lean_ctor_set(x_66, 39, x_63);
lean_ctor_set(x_66, 38, x_62);
lean_ctor_set(x_66, 37, x_61);
lean_ctor_set(x_66, 36, x_60);
lean_ctor_set(x_66, 34, x_58);
lean_ctor_set(x_66, 33, x_57);
lean_ctor_set(x_66, 32, x_56);
lean_ctor_set(x_66, 31, x_55);
lean_ctor_set(x_66, 30, x_54);
lean_ctor_set(x_66, 29, x_53);
lean_ctor_set(x_66, 28, x_52);
lean_ctor_set(x_66, 27, x_51);
lean_ctor_set(x_66, 26, x_50);
lean_ctor_set(x_66, 25, x_49);
lean_ctor_set(x_66, 24, x_48);
lean_ctor_set(x_66, 23, x_47);
lean_ctor_set(x_66, 22, x_46);
lean_ctor_set(x_66, 21, x_45);
lean_ctor_set(x_66, 20, x_44);
lean_ctor_set(x_66, 19, x_43);
lean_ctor_set(x_66, 18, x_42);
lean_ctor_set(x_66, 17, x_41);
lean_ctor_set(x_66, 16, x_40);
lean_ctor_set(x_66, 15, x_39);
lean_ctor_set(x_66, 14, x_38);
lean_ctor_set(x_66, 13, x_37);
lean_ctor_set(x_66, 12, x_36);
lean_ctor_set(x_66, 11, x_35);
lean_ctor_set(x_66, 10, x_34);
lean_ctor_set(x_66, 9, x_33);
lean_ctor_set(x_66, 8, x_32);
lean_ctor_set(x_66, 7, x_31);
lean_ctor_set(x_66, 6, x_30);
lean_ctor_set(x_66, 5, x_29);
lean_ctor_set(x_66, 4, x_28);
lean_ctor_set(x_66, 3, x_27);
lean_ctor_set(x_66, 2, x_26);
lean_ctor_set(x_66, 1, x_25);
lean_ctor_set(x_66, 0, x_24);
lean_ctor_set_uint8(x_66, sizeof(void*)*42, x_59);
x_111 = lean_array_fset(x_110, x_1, x_66);
lean_ctor_set(x_3, 0, x_111);
return x_3;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_66, 35);
lean_inc(x_112);
lean_dec(x_66);
x_113 = lean_box(0);
x_114 = lean_array_fset(x_4, x_1, x_113);
lean_inc_ref(x_65);
lean_inc_ref(x_64);
lean_inc(x_63);
lean_inc_ref(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_58);
lean_inc_ref(x_57);
lean_inc_ref(x_56);
lean_inc_ref(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_115 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_115, 0, x_24);
lean_ctor_set(x_115, 1, x_25);
lean_ctor_set(x_115, 2, x_26);
lean_ctor_set(x_115, 3, x_27);
lean_ctor_set(x_115, 4, x_28);
lean_ctor_set(x_115, 5, x_29);
lean_ctor_set(x_115, 6, x_30);
lean_ctor_set(x_115, 7, x_31);
lean_ctor_set(x_115, 8, x_32);
lean_ctor_set(x_115, 9, x_33);
lean_ctor_set(x_115, 10, x_34);
lean_ctor_set(x_115, 11, x_35);
lean_ctor_set(x_115, 12, x_36);
lean_ctor_set(x_115, 13, x_37);
lean_ctor_set(x_115, 14, x_38);
lean_ctor_set(x_115, 15, x_39);
lean_ctor_set(x_115, 16, x_40);
lean_ctor_set(x_115, 17, x_41);
lean_ctor_set(x_115, 18, x_42);
lean_ctor_set(x_115, 19, x_43);
lean_ctor_set(x_115, 20, x_44);
lean_ctor_set(x_115, 21, x_45);
lean_ctor_set(x_115, 22, x_46);
lean_ctor_set(x_115, 23, x_47);
lean_ctor_set(x_115, 24, x_48);
lean_ctor_set(x_115, 25, x_49);
lean_ctor_set(x_115, 26, x_50);
lean_ctor_set(x_115, 27, x_51);
lean_ctor_set(x_115, 28, x_52);
lean_ctor_set(x_115, 29, x_53);
lean_ctor_set(x_115, 30, x_54);
lean_ctor_set(x_115, 31, x_55);
lean_ctor_set(x_115, 32, x_56);
lean_ctor_set(x_115, 33, x_57);
lean_ctor_set(x_115, 34, x_58);
lean_ctor_set(x_115, 35, x_112);
lean_ctor_set(x_115, 36, x_60);
lean_ctor_set(x_115, 37, x_61);
lean_ctor_set(x_115, 38, x_62);
lean_ctor_set(x_115, 39, x_63);
lean_ctor_set(x_115, 40, x_64);
lean_ctor_set(x_115, 41, x_65);
lean_ctor_set_uint8(x_115, sizeof(void*)*42, x_59);
x_116 = lean_array_fset(x_114, x_1, x_115);
lean_ctor_set(x_3, 0, x_116);
return x_3;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_3);
x_117 = lean_ctor_get(x_2, 2);
x_118 = lean_ctor_get(x_117, 0);
x_119 = lean_ctor_get(x_117, 1);
x_120 = lean_ctor_get(x_117, 2);
x_121 = lean_ctor_get(x_117, 3);
x_122 = lean_ctor_get(x_117, 4);
x_123 = lean_ctor_get(x_117, 5);
x_124 = lean_ctor_get(x_117, 6);
x_125 = lean_ctor_get(x_117, 7);
x_126 = lean_ctor_get(x_117, 8);
x_127 = lean_ctor_get(x_117, 9);
x_128 = lean_ctor_get(x_117, 10);
x_129 = lean_ctor_get(x_117, 11);
x_130 = lean_ctor_get(x_117, 12);
x_131 = lean_ctor_get(x_117, 13);
x_132 = lean_ctor_get(x_117, 14);
x_133 = lean_ctor_get(x_117, 15);
x_134 = lean_ctor_get(x_117, 16);
x_135 = lean_ctor_get(x_117, 17);
x_136 = lean_ctor_get(x_117, 18);
x_137 = lean_ctor_get(x_117, 19);
x_138 = lean_ctor_get(x_117, 20);
x_139 = lean_ctor_get(x_117, 21);
x_140 = lean_ctor_get(x_117, 22);
x_141 = lean_ctor_get(x_117, 23);
x_142 = lean_ctor_get(x_117, 24);
x_143 = lean_ctor_get(x_117, 25);
x_144 = lean_ctor_get(x_117, 26);
x_145 = lean_ctor_get(x_117, 27);
x_146 = lean_ctor_get(x_117, 28);
x_147 = lean_ctor_get(x_117, 29);
x_148 = lean_ctor_get(x_117, 30);
x_149 = lean_ctor_get(x_117, 31);
x_150 = lean_ctor_get(x_117, 32);
x_151 = lean_ctor_get(x_117, 33);
x_152 = lean_ctor_get(x_117, 34);
x_153 = lean_ctor_get_uint8(x_117, sizeof(void*)*42);
x_154 = lean_ctor_get(x_117, 36);
x_155 = lean_ctor_get(x_117, 37);
x_156 = lean_ctor_get(x_117, 38);
x_157 = lean_ctor_get(x_117, 39);
x_158 = lean_ctor_get(x_117, 40);
x_159 = lean_ctor_get(x_117, 41);
x_160 = lean_array_fget(x_4, x_1);
x_161 = lean_ctor_get(x_160, 35);
lean_inc_ref(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 lean_ctor_release(x_160, 6);
 lean_ctor_release(x_160, 7);
 lean_ctor_release(x_160, 8);
 lean_ctor_release(x_160, 9);
 lean_ctor_release(x_160, 10);
 lean_ctor_release(x_160, 11);
 lean_ctor_release(x_160, 12);
 lean_ctor_release(x_160, 13);
 lean_ctor_release(x_160, 14);
 lean_ctor_release(x_160, 15);
 lean_ctor_release(x_160, 16);
 lean_ctor_release(x_160, 17);
 lean_ctor_release(x_160, 18);
 lean_ctor_release(x_160, 19);
 lean_ctor_release(x_160, 20);
 lean_ctor_release(x_160, 21);
 lean_ctor_release(x_160, 22);
 lean_ctor_release(x_160, 23);
 lean_ctor_release(x_160, 24);
 lean_ctor_release(x_160, 25);
 lean_ctor_release(x_160, 26);
 lean_ctor_release(x_160, 27);
 lean_ctor_release(x_160, 28);
 lean_ctor_release(x_160, 29);
 lean_ctor_release(x_160, 30);
 lean_ctor_release(x_160, 31);
 lean_ctor_release(x_160, 32);
 lean_ctor_release(x_160, 33);
 lean_ctor_release(x_160, 34);
 lean_ctor_release(x_160, 35);
 lean_ctor_release(x_160, 36);
 lean_ctor_release(x_160, 37);
 lean_ctor_release(x_160, 38);
 lean_ctor_release(x_160, 39);
 lean_ctor_release(x_160, 40);
 lean_ctor_release(x_160, 41);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
x_164 = lean_array_fset(x_4, x_1, x_163);
lean_inc_ref(x_159);
lean_inc_ref(x_158);
lean_inc(x_157);
lean_inc_ref(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_152);
lean_inc_ref(x_151);
lean_inc_ref(x_150);
lean_inc_ref(x_149);
lean_inc_ref(x_148);
lean_inc_ref(x_147);
lean_inc_ref(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc_ref(x_142);
lean_inc_ref(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
lean_inc(x_121);
lean_inc_ref(x_120);
lean_inc(x_119);
lean_inc(x_118);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 42, 1);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_118);
lean_ctor_set(x_165, 1, x_119);
lean_ctor_set(x_165, 2, x_120);
lean_ctor_set(x_165, 3, x_121);
lean_ctor_set(x_165, 4, x_122);
lean_ctor_set(x_165, 5, x_123);
lean_ctor_set(x_165, 6, x_124);
lean_ctor_set(x_165, 7, x_125);
lean_ctor_set(x_165, 8, x_126);
lean_ctor_set(x_165, 9, x_127);
lean_ctor_set(x_165, 10, x_128);
lean_ctor_set(x_165, 11, x_129);
lean_ctor_set(x_165, 12, x_130);
lean_ctor_set(x_165, 13, x_131);
lean_ctor_set(x_165, 14, x_132);
lean_ctor_set(x_165, 15, x_133);
lean_ctor_set(x_165, 16, x_134);
lean_ctor_set(x_165, 17, x_135);
lean_ctor_set(x_165, 18, x_136);
lean_ctor_set(x_165, 19, x_137);
lean_ctor_set(x_165, 20, x_138);
lean_ctor_set(x_165, 21, x_139);
lean_ctor_set(x_165, 22, x_140);
lean_ctor_set(x_165, 23, x_141);
lean_ctor_set(x_165, 24, x_142);
lean_ctor_set(x_165, 25, x_143);
lean_ctor_set(x_165, 26, x_144);
lean_ctor_set(x_165, 27, x_145);
lean_ctor_set(x_165, 28, x_146);
lean_ctor_set(x_165, 29, x_147);
lean_ctor_set(x_165, 30, x_148);
lean_ctor_set(x_165, 31, x_149);
lean_ctor_set(x_165, 32, x_150);
lean_ctor_set(x_165, 33, x_151);
lean_ctor_set(x_165, 34, x_152);
lean_ctor_set(x_165, 35, x_161);
lean_ctor_set(x_165, 36, x_154);
lean_ctor_set(x_165, 37, x_155);
lean_ctor_set(x_165, 38, x_156);
lean_ctor_set(x_165, 39, x_157);
lean_ctor_set(x_165, 40, x_158);
lean_ctor_set(x_165, 41, x_159);
lean_ctor_set_uint8(x_165, sizeof(void*)*42, x_153);
x_166 = lean_array_fset(x_164, x_1, x_165);
x_167 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_5);
lean_ctor_set(x_167, 2, x_6);
lean_ctor_set(x_167, 3, x_7);
lean_ctor_set(x_167, 4, x_8);
lean_ctor_set(x_167, 5, x_9);
lean_ctor_set(x_167, 6, x_10);
lean_ctor_set(x_167, 7, x_11);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentArray_isEmpty___redArg(x_6);
lean_dec_ref(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 2);
x_16 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_14);
x_19 = l_outOfBounds___redArg(x_16);
x_9 = x_19;
goto block_13;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_PersistentArray_get_x21___redArg(x_16, x_14, x_17);
x_9 = x_20;
goto block_13;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_12 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_11, x_10, x_3);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_1, x_2, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 5);
x_10 = lean_ctor_get(x_3, 6);
x_11 = lean_ctor_get(x_3, 7);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_1, x_12);
if (x_13 == 0)
{
return x_3;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_3, 7);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_4, x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 35);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_1, x_26);
x_28 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
x_29 = l_Lean_PersistentArray_set___redArg(x_25, x_2, x_28);
lean_ctor_set(x_23, 35, x_29);
x_30 = lean_array_fset(x_27, x_1, x_23);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
x_35 = lean_ctor_get(x_23, 4);
x_36 = lean_ctor_get(x_23, 5);
x_37 = lean_ctor_get(x_23, 6);
x_38 = lean_ctor_get(x_23, 7);
x_39 = lean_ctor_get(x_23, 8);
x_40 = lean_ctor_get(x_23, 9);
x_41 = lean_ctor_get(x_23, 10);
x_42 = lean_ctor_get(x_23, 11);
x_43 = lean_ctor_get(x_23, 12);
x_44 = lean_ctor_get(x_23, 13);
x_45 = lean_ctor_get(x_23, 14);
x_46 = lean_ctor_get(x_23, 15);
x_47 = lean_ctor_get(x_23, 16);
x_48 = lean_ctor_get(x_23, 17);
x_49 = lean_ctor_get(x_23, 18);
x_50 = lean_ctor_get(x_23, 19);
x_51 = lean_ctor_get(x_23, 20);
x_52 = lean_ctor_get(x_23, 21);
x_53 = lean_ctor_get(x_23, 22);
x_54 = lean_ctor_get(x_23, 23);
x_55 = lean_ctor_get(x_23, 24);
x_56 = lean_ctor_get(x_23, 25);
x_57 = lean_ctor_get(x_23, 26);
x_58 = lean_ctor_get(x_23, 27);
x_59 = lean_ctor_get(x_23, 28);
x_60 = lean_ctor_get(x_23, 29);
x_61 = lean_ctor_get(x_23, 30);
x_62 = lean_ctor_get(x_23, 31);
x_63 = lean_ctor_get(x_23, 32);
x_64 = lean_ctor_get(x_23, 33);
x_65 = lean_ctor_get(x_23, 34);
x_66 = lean_ctor_get(x_23, 35);
x_67 = lean_ctor_get_uint8(x_23, sizeof(void*)*42);
x_68 = lean_ctor_get(x_23, 36);
x_69 = lean_ctor_get(x_23, 37);
x_70 = lean_ctor_get(x_23, 38);
x_71 = lean_ctor_get(x_23, 39);
x_72 = lean_ctor_get(x_23, 40);
x_73 = lean_ctor_get(x_23, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
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
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
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
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_4, x_1, x_74);
x_76 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
x_77 = l_Lean_PersistentArray_set___redArg(x_66, x_2, x_76);
x_78 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_78, 0, x_31);
lean_ctor_set(x_78, 1, x_32);
lean_ctor_set(x_78, 2, x_33);
lean_ctor_set(x_78, 3, x_34);
lean_ctor_set(x_78, 4, x_35);
lean_ctor_set(x_78, 5, x_36);
lean_ctor_set(x_78, 6, x_37);
lean_ctor_set(x_78, 7, x_38);
lean_ctor_set(x_78, 8, x_39);
lean_ctor_set(x_78, 9, x_40);
lean_ctor_set(x_78, 10, x_41);
lean_ctor_set(x_78, 11, x_42);
lean_ctor_set(x_78, 12, x_43);
lean_ctor_set(x_78, 13, x_44);
lean_ctor_set(x_78, 14, x_45);
lean_ctor_set(x_78, 15, x_46);
lean_ctor_set(x_78, 16, x_47);
lean_ctor_set(x_78, 17, x_48);
lean_ctor_set(x_78, 18, x_49);
lean_ctor_set(x_78, 19, x_50);
lean_ctor_set(x_78, 20, x_51);
lean_ctor_set(x_78, 21, x_52);
lean_ctor_set(x_78, 22, x_53);
lean_ctor_set(x_78, 23, x_54);
lean_ctor_set(x_78, 24, x_55);
lean_ctor_set(x_78, 25, x_56);
lean_ctor_set(x_78, 26, x_57);
lean_ctor_set(x_78, 27, x_58);
lean_ctor_set(x_78, 28, x_59);
lean_ctor_set(x_78, 29, x_60);
lean_ctor_set(x_78, 30, x_61);
lean_ctor_set(x_78, 31, x_62);
lean_ctor_set(x_78, 32, x_63);
lean_ctor_set(x_78, 33, x_64);
lean_ctor_set(x_78, 34, x_65);
lean_ctor_set(x_78, 35, x_77);
lean_ctor_set(x_78, 36, x_68);
lean_ctor_set(x_78, 37, x_69);
lean_ctor_set(x_78, 38, x_70);
lean_ctor_set(x_78, 39, x_71);
lean_ctor_set(x_78, 40, x_72);
lean_ctor_set(x_78, 41, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*42, x_67);
x_79 = lean_array_fset(x_75, x_1, x_78);
lean_ctor_set(x_3, 0, x_79);
return x_3;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
x_80 = lean_array_fget(x_4, x_1);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 7);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 8);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 9);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 11);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 12);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 13);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 14);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 15);
lean_inc(x_96);
x_97 = lean_ctor_get(x_80, 16);
lean_inc(x_97);
x_98 = lean_ctor_get(x_80, 17);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_80, 18);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_80, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 20);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 21);
lean_inc(x_102);
x_103 = lean_ctor_get(x_80, 22);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_80, 23);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_80, 24);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_80, 25);
lean_inc(x_106);
x_107 = lean_ctor_get(x_80, 26);
lean_inc(x_107);
x_108 = lean_ctor_get(x_80, 27);
lean_inc(x_108);
x_109 = lean_ctor_get(x_80, 28);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_80, 29);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_80, 30);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_80, 31);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_80, 32);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_80, 33);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_80, 34);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_80, 35);
lean_inc_ref(x_116);
x_117 = lean_ctor_get_uint8(x_80, sizeof(void*)*42);
x_118 = lean_ctor_get(x_80, 36);
lean_inc(x_118);
x_119 = lean_ctor_get(x_80, 37);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_80, 38);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_80, 39);
lean_inc(x_121);
x_122 = lean_ctor_get(x_80, 40);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_80, 41);
lean_inc_ref(x_123);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 lean_ctor_release(x_80, 6);
 lean_ctor_release(x_80, 7);
 lean_ctor_release(x_80, 8);
 lean_ctor_release(x_80, 9);
 lean_ctor_release(x_80, 10);
 lean_ctor_release(x_80, 11);
 lean_ctor_release(x_80, 12);
 lean_ctor_release(x_80, 13);
 lean_ctor_release(x_80, 14);
 lean_ctor_release(x_80, 15);
 lean_ctor_release(x_80, 16);
 lean_ctor_release(x_80, 17);
 lean_ctor_release(x_80, 18);
 lean_ctor_release(x_80, 19);
 lean_ctor_release(x_80, 20);
 lean_ctor_release(x_80, 21);
 lean_ctor_release(x_80, 22);
 lean_ctor_release(x_80, 23);
 lean_ctor_release(x_80, 24);
 lean_ctor_release(x_80, 25);
 lean_ctor_release(x_80, 26);
 lean_ctor_release(x_80, 27);
 lean_ctor_release(x_80, 28);
 lean_ctor_release(x_80, 29);
 lean_ctor_release(x_80, 30);
 lean_ctor_release(x_80, 31);
 lean_ctor_release(x_80, 32);
 lean_ctor_release(x_80, 33);
 lean_ctor_release(x_80, 34);
 lean_ctor_release(x_80, 35);
 lean_ctor_release(x_80, 36);
 lean_ctor_release(x_80, 37);
 lean_ctor_release(x_80, 38);
 lean_ctor_release(x_80, 39);
 lean_ctor_release(x_80, 40);
 lean_ctor_release(x_80, 41);
 x_124 = x_80;
} else {
 lean_dec_ref(x_80);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
x_126 = lean_array_fset(x_4, x_1, x_125);
x_127 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3;
x_128 = l_Lean_PersistentArray_set___redArg(x_116, x_2, x_127);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 42, 1);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_81);
lean_ctor_set(x_129, 1, x_82);
lean_ctor_set(x_129, 2, x_83);
lean_ctor_set(x_129, 3, x_84);
lean_ctor_set(x_129, 4, x_85);
lean_ctor_set(x_129, 5, x_86);
lean_ctor_set(x_129, 6, x_87);
lean_ctor_set(x_129, 7, x_88);
lean_ctor_set(x_129, 8, x_89);
lean_ctor_set(x_129, 9, x_90);
lean_ctor_set(x_129, 10, x_91);
lean_ctor_set(x_129, 11, x_92);
lean_ctor_set(x_129, 12, x_93);
lean_ctor_set(x_129, 13, x_94);
lean_ctor_set(x_129, 14, x_95);
lean_ctor_set(x_129, 15, x_96);
lean_ctor_set(x_129, 16, x_97);
lean_ctor_set(x_129, 17, x_98);
lean_ctor_set(x_129, 18, x_99);
lean_ctor_set(x_129, 19, x_100);
lean_ctor_set(x_129, 20, x_101);
lean_ctor_set(x_129, 21, x_102);
lean_ctor_set(x_129, 22, x_103);
lean_ctor_set(x_129, 23, x_104);
lean_ctor_set(x_129, 24, x_105);
lean_ctor_set(x_129, 25, x_106);
lean_ctor_set(x_129, 26, x_107);
lean_ctor_set(x_129, 27, x_108);
lean_ctor_set(x_129, 28, x_109);
lean_ctor_set(x_129, 29, x_110);
lean_ctor_set(x_129, 30, x_111);
lean_ctor_set(x_129, 31, x_112);
lean_ctor_set(x_129, 32, x_113);
lean_ctor_set(x_129, 33, x_114);
lean_ctor_set(x_129, 34, x_115);
lean_ctor_set(x_129, 35, x_128);
lean_ctor_set(x_129, 36, x_118);
lean_ctor_set(x_129, 37, x_119);
lean_ctor_set(x_129, 38, x_120);
lean_ctor_set(x_129, 39, x_121);
lean_ctor_set(x_129, 40, x_122);
lean_ctor_set(x_129, 41, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*42, x_117);
x_130 = lean_array_fset(x_126, x_1, x_129);
x_131 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_5);
lean_ctor_set(x_131, 2, x_6);
lean_ctor_set(x_131, 3, x_7);
lean_ctor_set(x_131, 4, x_8);
lean_ctor_set(x_131, 5, x_9);
lean_ctor_set(x_131, 6, x_10);
lean_ctor_set(x_131, 7, x_11);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_4, 4);
x_10 = lean_ctor_get(x_4, 5);
x_11 = lean_ctor_get(x_4, 6);
x_12 = lean_ctor_get(x_4, 7);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
uint8_t x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_4, 7);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_5, x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 35);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_5, x_1, x_27);
x_29 = l_Lean_PersistentArray_set___redArg(x_26, x_2, x_3);
lean_ctor_set(x_24, 35, x_29);
x_30 = lean_array_fset(x_28, x_1, x_24);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_ctor_get(x_24, 2);
x_34 = lean_ctor_get(x_24, 3);
x_35 = lean_ctor_get(x_24, 4);
x_36 = lean_ctor_get(x_24, 5);
x_37 = lean_ctor_get(x_24, 6);
x_38 = lean_ctor_get(x_24, 7);
x_39 = lean_ctor_get(x_24, 8);
x_40 = lean_ctor_get(x_24, 9);
x_41 = lean_ctor_get(x_24, 10);
x_42 = lean_ctor_get(x_24, 11);
x_43 = lean_ctor_get(x_24, 12);
x_44 = lean_ctor_get(x_24, 13);
x_45 = lean_ctor_get(x_24, 14);
x_46 = lean_ctor_get(x_24, 15);
x_47 = lean_ctor_get(x_24, 16);
x_48 = lean_ctor_get(x_24, 17);
x_49 = lean_ctor_get(x_24, 18);
x_50 = lean_ctor_get(x_24, 19);
x_51 = lean_ctor_get(x_24, 20);
x_52 = lean_ctor_get(x_24, 21);
x_53 = lean_ctor_get(x_24, 22);
x_54 = lean_ctor_get(x_24, 23);
x_55 = lean_ctor_get(x_24, 24);
x_56 = lean_ctor_get(x_24, 25);
x_57 = lean_ctor_get(x_24, 26);
x_58 = lean_ctor_get(x_24, 27);
x_59 = lean_ctor_get(x_24, 28);
x_60 = lean_ctor_get(x_24, 29);
x_61 = lean_ctor_get(x_24, 30);
x_62 = lean_ctor_get(x_24, 31);
x_63 = lean_ctor_get(x_24, 32);
x_64 = lean_ctor_get(x_24, 33);
x_65 = lean_ctor_get(x_24, 34);
x_66 = lean_ctor_get(x_24, 35);
x_67 = lean_ctor_get_uint8(x_24, sizeof(void*)*42);
x_68 = lean_ctor_get(x_24, 36);
x_69 = lean_ctor_get(x_24, 37);
x_70 = lean_ctor_get(x_24, 38);
x_71 = lean_ctor_get(x_24, 39);
x_72 = lean_ctor_get(x_24, 40);
x_73 = lean_ctor_get(x_24, 41);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
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
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
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
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_5, x_1, x_74);
x_76 = l_Lean_PersistentArray_set___redArg(x_66, x_2, x_3);
x_77 = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_32);
lean_ctor_set(x_77, 2, x_33);
lean_ctor_set(x_77, 3, x_34);
lean_ctor_set(x_77, 4, x_35);
lean_ctor_set(x_77, 5, x_36);
lean_ctor_set(x_77, 6, x_37);
lean_ctor_set(x_77, 7, x_38);
lean_ctor_set(x_77, 8, x_39);
lean_ctor_set(x_77, 9, x_40);
lean_ctor_set(x_77, 10, x_41);
lean_ctor_set(x_77, 11, x_42);
lean_ctor_set(x_77, 12, x_43);
lean_ctor_set(x_77, 13, x_44);
lean_ctor_set(x_77, 14, x_45);
lean_ctor_set(x_77, 15, x_46);
lean_ctor_set(x_77, 16, x_47);
lean_ctor_set(x_77, 17, x_48);
lean_ctor_set(x_77, 18, x_49);
lean_ctor_set(x_77, 19, x_50);
lean_ctor_set(x_77, 20, x_51);
lean_ctor_set(x_77, 21, x_52);
lean_ctor_set(x_77, 22, x_53);
lean_ctor_set(x_77, 23, x_54);
lean_ctor_set(x_77, 24, x_55);
lean_ctor_set(x_77, 25, x_56);
lean_ctor_set(x_77, 26, x_57);
lean_ctor_set(x_77, 27, x_58);
lean_ctor_set(x_77, 28, x_59);
lean_ctor_set(x_77, 29, x_60);
lean_ctor_set(x_77, 30, x_61);
lean_ctor_set(x_77, 31, x_62);
lean_ctor_set(x_77, 32, x_63);
lean_ctor_set(x_77, 33, x_64);
lean_ctor_set(x_77, 34, x_65);
lean_ctor_set(x_77, 35, x_76);
lean_ctor_set(x_77, 36, x_68);
lean_ctor_set(x_77, 37, x_69);
lean_ctor_set(x_77, 38, x_70);
lean_ctor_set(x_77, 39, x_71);
lean_ctor_set(x_77, 40, x_72);
lean_ctor_set(x_77, 41, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*42, x_67);
x_78 = lean_array_fset(x_75, x_1, x_77);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_79 = lean_array_fget(x_5, x_1);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 12);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 13);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 14);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 15);
lean_inc(x_95);
x_96 = lean_ctor_get(x_79, 16);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 17);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_79, 18);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_79, 19);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 20);
lean_inc(x_100);
x_101 = lean_ctor_get(x_79, 21);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 22);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_79, 23);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_79, 24);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_79, 25);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 26);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 27);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 28);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_79, 29);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_79, 30);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_79, 31);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_79, 32);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_79, 33);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_79, 34);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_79, 35);
lean_inc_ref(x_115);
x_116 = lean_ctor_get_uint8(x_79, sizeof(void*)*42);
x_117 = lean_ctor_get(x_79, 36);
lean_inc(x_117);
x_118 = lean_ctor_get(x_79, 37);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_79, 38);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_79, 39);
lean_inc(x_120);
x_121 = lean_ctor_get(x_79, 40);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_79, 41);
lean_inc_ref(x_122);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 lean_ctor_release(x_79, 6);
 lean_ctor_release(x_79, 7);
 lean_ctor_release(x_79, 8);
 lean_ctor_release(x_79, 9);
 lean_ctor_release(x_79, 10);
 lean_ctor_release(x_79, 11);
 lean_ctor_release(x_79, 12);
 lean_ctor_release(x_79, 13);
 lean_ctor_release(x_79, 14);
 lean_ctor_release(x_79, 15);
 lean_ctor_release(x_79, 16);
 lean_ctor_release(x_79, 17);
 lean_ctor_release(x_79, 18);
 lean_ctor_release(x_79, 19);
 lean_ctor_release(x_79, 20);
 lean_ctor_release(x_79, 21);
 lean_ctor_release(x_79, 22);
 lean_ctor_release(x_79, 23);
 lean_ctor_release(x_79, 24);
 lean_ctor_release(x_79, 25);
 lean_ctor_release(x_79, 26);
 lean_ctor_release(x_79, 27);
 lean_ctor_release(x_79, 28);
 lean_ctor_release(x_79, 29);
 lean_ctor_release(x_79, 30);
 lean_ctor_release(x_79, 31);
 lean_ctor_release(x_79, 32);
 lean_ctor_release(x_79, 33);
 lean_ctor_release(x_79, 34);
 lean_ctor_release(x_79, 35);
 lean_ctor_release(x_79, 36);
 lean_ctor_release(x_79, 37);
 lean_ctor_release(x_79, 38);
 lean_ctor_release(x_79, 39);
 lean_ctor_release(x_79, 40);
 lean_ctor_release(x_79, 41);
 x_123 = x_79;
} else {
 lean_dec_ref(x_79);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_array_fset(x_5, x_1, x_124);
x_126 = l_Lean_PersistentArray_set___redArg(x_115, x_2, x_3);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 42, 1);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_80);
lean_ctor_set(x_127, 1, x_81);
lean_ctor_set(x_127, 2, x_82);
lean_ctor_set(x_127, 3, x_83);
lean_ctor_set(x_127, 4, x_84);
lean_ctor_set(x_127, 5, x_85);
lean_ctor_set(x_127, 6, x_86);
lean_ctor_set(x_127, 7, x_87);
lean_ctor_set(x_127, 8, x_88);
lean_ctor_set(x_127, 9, x_89);
lean_ctor_set(x_127, 10, x_90);
lean_ctor_set(x_127, 11, x_91);
lean_ctor_set(x_127, 12, x_92);
lean_ctor_set(x_127, 13, x_93);
lean_ctor_set(x_127, 14, x_94);
lean_ctor_set(x_127, 15, x_95);
lean_ctor_set(x_127, 16, x_96);
lean_ctor_set(x_127, 17, x_97);
lean_ctor_set(x_127, 18, x_98);
lean_ctor_set(x_127, 19, x_99);
lean_ctor_set(x_127, 20, x_100);
lean_ctor_set(x_127, 21, x_101);
lean_ctor_set(x_127, 22, x_102);
lean_ctor_set(x_127, 23, x_103);
lean_ctor_set(x_127, 24, x_104);
lean_ctor_set(x_127, 25, x_105);
lean_ctor_set(x_127, 26, x_106);
lean_ctor_set(x_127, 27, x_107);
lean_ctor_set(x_127, 28, x_108);
lean_ctor_set(x_127, 29, x_109);
lean_ctor_set(x_127, 30, x_110);
lean_ctor_set(x_127, 31, x_111);
lean_ctor_set(x_127, 32, x_112);
lean_ctor_set(x_127, 33, x_113);
lean_ctor_set(x_127, 34, x_114);
lean_ctor_set(x_127, 35, x_126);
lean_ctor_set(x_127, 36, x_117);
lean_ctor_set(x_127, 37, x_118);
lean_ctor_set(x_127, 38, x_119);
lean_ctor_set(x_127, 39, x_120);
lean_ctor_set(x_127, 40, x_121);
lean_ctor_set(x_127, 41, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*42, x_116);
x_128 = lean_array_fset(x_125, x_1, x_127);
x_129 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_6);
lean_ctor_set(x_129, 2, x_7);
lean_ctor_set(x_129, 3, x_8);
lean_ctor_set(x_129, 4, x_9);
lean_ctor_set(x_129, 5, x_10);
lean_ctor_set(x_129, 6, x_11);
lean_ctor_set(x_129, 7, x_12);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` internal error, eliminated variable must have equation associated with it", 81, 81);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_51; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_51 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_63 = lean_ctor_get(x_52, 38);
lean_inc_ref(x_63);
lean_dec(x_52);
x_64 = lean_ctor_get(x_63, 2);
x_65 = lean_box(0);
x_66 = lean_nat_dec_lt(x_16, x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_63);
x_67 = l_outOfBounds___redArg(x_65);
x_53 = x_67;
goto block_62;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_PersistentArray_get_x21___redArg(x_65, x_63, x_16);
x_53 = x_68;
goto block_62;
}
block_62:
{
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_ctor_get(x_54, 0);
x_56 = l_Lean_Grind_Linarith_Poly_coeff(x_55, x_16);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9;
x_58 = lean_int_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_inc(x_55);
x_18 = x_54;
x_19 = x_55;
x_20 = x_56;
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_12;
x_32 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_17);
lean_dec(x_16);
x_59 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_54);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1;
x_61 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__1___redArg(x_60, x_9, x_10, x_11, x_12);
return x_61;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
block_50:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_16);
lean_inc(x_22);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__0___boxed), 3, 2);
lean_closure_set(x_33, 0, x_22);
lean_closure_set(x_33, 1, x_16);
x_34 = l_Lean_Meta_Grind_Arith_Linear_linearExt;
x_35 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_34, x_33, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Lean_Grind_Linarith_Poly_eval_x3f(x_19, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_18);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Rat_neg(x_38);
x_40 = l_Rat_ofInt(x_20);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
lean_inc_ref(x_41);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment(x_16, x_41, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_42);
lean_inc(x_22);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___lam__1___boxed), 4, 3);
lean_closure_set(x_43, 0, x_22);
lean_closure_set(x_43, 1, x_16);
lean_closure_set(x_43, 2, x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_34, x_43, x_23);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_1 = x_17;
x_2 = x_21;
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
x_6 = x_25;
x_7 = x_26;
x_8 = x_27;
x_9 = x_28;
x_10 = x_29;
x_11 = x_30;
x_12 = x_31;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_17);
return x_44;
}
}
else
{
lean_dec_ref(x_41);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
return x_42;
}
}
else
{
lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_46 = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_throwUnexpected___redArg(x_18, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
lean_dec(x_22);
lean_dec_ref(x_18);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_inconsistent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_13);
x_17 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 39);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 39);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go(x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_32 = x_27;
} else {
 lean_dec_ref(x_27);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("next var: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found assignment", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main loop", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_220; 
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_59 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_220 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_12);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
x_70 = x_13;
x_71 = lean_box(0);
goto block_219;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6;
x_224 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_223, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_224) == 0)
{
lean_dec_ref(x_224);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
x_70 = x_13;
x_71 = lean_box(0);
goto block_219;
}
else
{
uint8_t x_225; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
return x_224;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = !lean_is_exclusive(x_220);
if (x_228 == 0)
{
return x_220;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_220, 0);
lean_inc(x_229);
lean_dec(x_220);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
block_38:
{
lean_object* x_27; 
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_32 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
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
block_57:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_Grind_Arith_Linear_processVar(x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
lean_dec(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
block_219:
{
lean_object* x_72; 
x_72 = l_Lean_Core_checkSystem(x_58, x_69, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_dec_ref(x_72);
x_73 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Lean_Meta_Grind_isInconsistent___redArg(x_62);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_free_object(x_76);
x_80 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_ctor_get(x_81, 36);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_83, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_82);
x_89 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_90, 35);
lean_inc_ref(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
lean_dec_ref(x_92);
x_39 = x_95;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
lean_dec_ref(x_92);
x_97 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_96, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_100, 35);
lean_inc_ref(x_101);
lean_dec(x_100);
x_102 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2;
x_103 = l_Lean_MessageData_ofExpr(x_98);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_96);
x_107 = l_Nat_reprFast(x_96);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Lean_MessageData_ofFormat(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
x_112 = l_Lean_PersistentArray_toList___redArg(x_101);
lean_dec_ref(x_101);
x_113 = lean_box(0);
x_114 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_112, x_113);
x_115 = l_Lean_MessageData_ofList(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_116, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_39 = x_96;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
uint8_t x_118; 
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
return x_117;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_99);
if (x_121 == 0)
{
return x_99;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
lean_dec(x_99);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_97);
if (x_124 == 0)
{
return x_97;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_97, 0);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_90);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_91);
if (x_127 == 0)
{
return x_91;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_91, 0);
lean_inc(x_128);
lean_dec(x_91);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = !lean_is_exclusive(x_89);
if (x_130 == 0)
{
return x_89;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_89, 0);
lean_inc(x_131);
lean_dec(x_89);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_80);
if (x_133 == 0)
{
return x_80;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_80, 0);
lean_inc(x_134);
lean_dec(x_80);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_1);
lean_ctor_set(x_76, 0, x_137);
return x_76;
}
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_76, 0);
lean_inc(x_138);
lean_dec(x_76);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 36);
lean_inc(x_142);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 1)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_143, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_144) == 0)
{
lean_dec_ref(x_144);
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_142);
x_149 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_150, 35);
lean_inc_ref(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_152, 2);
lean_inc(x_155);
lean_dec_ref(x_152);
x_39 = x_155;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_152, 2);
lean_inc(x_156);
lean_dec_ref(x_152);
x_157 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_156, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = lean_ctor_get(x_160, 35);
lean_inc_ref(x_161);
lean_dec(x_160);
x_162 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2;
x_163 = l_Lean_MessageData_ofExpr(x_158);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_inc(x_156);
x_167 = l_Nat_reprFast(x_156);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Lean_MessageData_ofFormat(x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
x_172 = l_Lean_PersistentArray_toList___redArg(x_161);
lean_dec_ref(x_161);
x_173 = lean_box(0);
x_174 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_172, x_173);
x_175 = l_Lean_MessageData_ofList(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_176, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_177) == 0)
{
lean_dec_ref(x_177);
x_39 = x_156;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_ctor_get(x_159, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_182 = x_159;
} else {
 lean_dec_ref(x_159);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_157, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_185 = x_157;
} else {
 lean_dec_ref(x_157);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_150);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_151, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_188 = x_151;
} else {
 lean_dec_ref(x_151);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_149, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_191 = x_149;
} else {
 lean_dec_ref(x_149);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_ctor_get(x_140, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_194 = x_140;
} else {
 lean_dec_ref(x_140);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_1);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_76);
if (x_199 == 0)
{
return x_76;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_76, 0);
lean_inc(x_200);
lean_dec(x_76);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_202 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
x_15 = x_60;
x_16 = x_61;
x_17 = x_62;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4;
x_206 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_205, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_15 = x_60;
x_16 = x_61;
x_17 = x_62;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_207; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_210 = !lean_is_exclusive(x_202);
if (x_210 == 0)
{
return x_202;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_202, 0);
lean_inc(x_211);
lean_dec(x_202);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_73);
if (x_213 == 0)
{
return x_73;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_73, 0);
lean_inc(x_214);
lean_dec(x_73);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_72);
if (x_216 == 0)
{
return x_72;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_72, 0);
lean_inc(x_217);
lean_dec(x_72);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_220; 
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2;
x_59 = l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2;
x_220 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_12);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
x_70 = x_13;
x_71 = lean_box(0);
goto block_219;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6;
x_224 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_223, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_224) == 0)
{
lean_dec_ref(x_224);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = x_3;
x_61 = x_4;
x_62 = x_5;
x_63 = x_6;
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
x_70 = x_13;
x_71 = lean_box(0);
goto block_219;
}
else
{
uint8_t x_225; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
return x_224;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = !lean_is_exclusive(x_220);
if (x_228 == 0)
{
return x_220;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_220, 0);
lean_inc(x_229);
lean_dec(x_220);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
}
block_38:
{
lean_object* x_27; 
x_27 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_32 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
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
block_57:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_Grind_Arith_Linear_processVar(x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
lean_dec(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec_ref(x_52);
x_53 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
block_219:
{
lean_object* x_72; 
x_72 = l_Lean_Core_checkSystem(x_58, x_69, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_dec_ref(x_72);
x_73 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Lean_Meta_Grind_isInconsistent___redArg(x_62);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_free_object(x_76);
x_80 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_ctor_get(x_81, 36);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_83, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec_ref(x_84);
x_85 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_82);
x_89 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_90, 35);
lean_inc_ref(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
lean_dec_ref(x_92);
x_39 = x_95;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
lean_dec_ref(x_92);
x_97 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_96, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_100, 35);
lean_inc_ref(x_101);
lean_dec(x_100);
x_102 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2;
x_103 = l_Lean_MessageData_ofExpr(x_98);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_96);
x_107 = l_Nat_reprFast(x_96);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Lean_MessageData_ofFormat(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
x_112 = l_Lean_PersistentArray_toList___redArg(x_101);
lean_dec_ref(x_101);
x_113 = lean_box(0);
x_114 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_112, x_113);
x_115 = l_Lean_MessageData_ofList(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_116, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_39 = x_96;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
uint8_t x_118; 
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
return x_117;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_99);
if (x_121 == 0)
{
return x_99;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
lean_dec(x_99);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_96);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_97);
if (x_124 == 0)
{
return x_97;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_97, 0);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_90);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_91);
if (x_127 == 0)
{
return x_91;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_91, 0);
lean_inc(x_128);
lean_dec(x_91);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = !lean_is_exclusive(x_89);
if (x_130 == 0)
{
return x_89;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_89, 0);
lean_inc(x_131);
lean_dec(x_89);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_80);
if (x_133 == 0)
{
return x_80;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_80, 0);
lean_inc(x_134);
lean_dec(x_80);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_1);
lean_ctor_set(x_76, 0, x_137);
return x_76;
}
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_76, 0);
lean_inc(x_138);
lean_dec(x_76);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 36);
lean_inc(x_142);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 1)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_Meta_Grind_Arith_Linear_resolveConflict(x_143, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec_ref(x_144);
x_145 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_142);
x_149 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_150, 35);
lean_inc_ref(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_152, 2);
lean_inc(x_155);
lean_dec_ref(x_152);
x_39 = x_155;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_152, 2);
lean_inc(x_156);
lean_dec_ref(x_152);
x_157 = l_Lean_Meta_Grind_Arith_Linear_getVar(x_156, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = lean_ctor_get(x_160, 35);
lean_inc_ref(x_161);
lean_dec(x_160);
x_162 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2;
x_163 = l_Lean_MessageData_ofExpr(x_158);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_inc(x_156);
x_167 = l_Nat_reprFast(x_156);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Lean_MessageData_ofFormat(x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
x_172 = l_Lean_PersistentArray_toList___redArg(x_161);
lean_dec_ref(x_161);
x_173 = lean_box(0);
x_174 = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Linear_processVar_spec__1(x_172, x_173);
x_175 = l_Lean_MessageData_ofList(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_176, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_177) == 0)
{
lean_dec_ref(x_177);
x_39 = x_156;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_68;
x_49 = x_69;
x_50 = x_70;
x_51 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_ctor_get(x_159, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_182 = x_159;
} else {
 lean_dec_ref(x_159);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_156);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_157, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_185 = x_157;
} else {
 lean_dec_ref(x_157);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_150);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_151, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_188 = x_151;
} else {
 lean_dec_ref(x_151);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_149, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_191 = x_149;
} else {
 lean_dec_ref(x_149);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_ctor_get(x_140, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_194 = x_140;
} else {
 lean_dec_ref(x_140);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_1);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_76);
if (x_199 == 0)
{
return x_76;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_76, 0);
lean_inc(x_200);
lean_dec(x_76);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_202 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__1___redArg(x_59, x_69);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
x_15 = x_60;
x_16 = x_61;
x_17 = x_62;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4;
x_206 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__3___redArg(x_59, x_205, x_67, x_68, x_69, x_70);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_15 = x_60;
x_16 = x_61;
x_17 = x_62;
x_18 = x_63;
x_19 = x_64;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_207; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_210 = !lean_is_exclusive(x_202);
if (x_210 == 0)
{
return x_202;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_202, 0);
lean_inc(x_211);
lean_dec(x_202);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_73);
if (x_213 == 0)
{
return x_73;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_73, 0);
lean_inc(x_214);
lean_dec(x_73);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_72);
if (x_216 == 0)
{
return x_72;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_72, 0);
lean_inc(x_217);
lean_dec(x_72);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0;
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_25; 
x_25 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___redArg(x_1, x_2, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0___boxed(lean_object** _args) {
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
lean_object* x_24 = _args[23];
_start:
{
lean_object* x_25; 
x_25 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3;
x_13 = lean_st_mk_ref(x_12);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_13);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_resetDecisionStack___redArg(x_13, x_1, x_2);
lean_dec(x_2);
x_14 = x_22;
goto block_20;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_21;
goto block_20;
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_st_ref_get(x_13);
lean_dec(x_13);
lean_dec(x_16);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_get(x_13);
lean_dec(x_13);
lean_dec(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
}
else
{
lean_dec(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_15, x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; uint8_t x_45; 
x_45 = lean_nat_dec_lt(x_4, x_1);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_5);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_53; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_dec_ref(x_5);
x_53 = l_Lean_Meta_Grind_Arith_Linear_hasAssignment(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_48 = x_45;
x_49 = lean_box(0);
goto block_52;
}
else
{
uint8_t x_57; 
lean_dec(x_47);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
x_48 = x_3;
x_49 = lean_box(0);
goto block_52;
}
}
else
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec_ref(x_53);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
x_48 = x_61;
x_49 = lean_box(0);
goto block_52;
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
block_52:
{
uint8_t x_50; 
x_50 = lean_unbox(x_47);
if (x_50 == 0)
{
lean_dec(x_47);
x_16 = lean_box(0);
x_17 = x_48;
goto block_44;
}
else
{
uint8_t x_51; 
x_51 = lean_unbox(x_47);
lean_dec(x_47);
x_16 = lean_box(0);
x_17 = x_51;
goto block_44;
}
}
}
block_44:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Grind_isInconsistent___redArg(x_6);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
lean_dec(x_20);
x_22 = lean_box(x_17);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_20);
x_28 = lean_box(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_unbox(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_32 = lean_box(x_17);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_4, x_34);
lean_dec(x_4);
x_4 = x_35;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_30);
x_38 = lean_box(x_17);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(x_2, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_15, x_17, x_1, x_16, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; 
lean_inc_ref(x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_27);
lean_dec(x_26);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Linear_check___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_check___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind linarith", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_check___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_check___lam__0___boxed), 11, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_11);
x_12 = l_Lean_Meta_Grind_Arith_Linear_check___closed__0;
x_13 = l_Lean_Meta_Grind_Arith_Linear_check___closed__1;
x_14 = lean_box(0);
x_15 = l_Lean_profileitM___at___00Lean_Meta_Grind_Arith_Linear_check_spec__1___redArg(x_12, x_11, x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Linear_check(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_3);
x_20 = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_check_spec__0(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_1);
return x_20;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLtFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_Linarith_Poly_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__2_spec__5___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getLeFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected_spec__0_spec__0_spec__1___closed__1);
l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_throwUnexpected___redArg___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_throwUnexpected_spec__0_spec__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_checkIsNextVar___closed__1);
l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0 = _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__0);
l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1 = _init_l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__0___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment_spec__1___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_traceAssignment___closed__10);
l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getBestLower_x3f___closed__0);
l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_getDiseqValues___closed__0);
l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_findDiseq_x3f___closed__0);
l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_geAvoiding___closed__0);
l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__0);
l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__1);
l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__2);
l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveLowerUpperConflict___closed__3);
l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_findRat___closed__0);
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split_spec__4_spec__7___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__0);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__1);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__2);
l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_split___closed__3);
l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveLowerDiseqConflict___closed__0);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__0);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__1);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__2);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__3);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__4);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__5);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__6);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__7);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__8);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__9);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__10);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__11);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__12);
l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13 = _init_l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_processVar___closed__13);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__0);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__1);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__2);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__3);
l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4 = _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__3___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__3);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase_spec__2_spec__2___redArg___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_findCase___closed__4);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__0);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__1);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__2);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__3);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__4);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__5);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__6);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__7);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__8);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__9);
l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10 = _init_l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_resolveConflict___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_assignElimVars_go___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__3);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__5);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain_spec__0_spec__0___redArg___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignmentMain___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Search_0__Lean_Meta_Grind_Arith_Linear_searchAssignment___closed__3);
l_Lean_Meta_Grind_Arith_Linear_check___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_check___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_check___closed__0);
l_Lean_Meta_Grind_Arith_Linear_check___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_check___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_check___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
