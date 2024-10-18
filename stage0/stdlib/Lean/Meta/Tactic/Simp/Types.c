// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Types
// Imports: Lean.Meta.AppBuilder Lean.Meta.CongrTheorems Lean.Meta.Eqns Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_recordSimpTheorem___closed__1;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__8;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__2;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__4;
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6;
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__4;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__9;
static lean_object* l_Lean_Meta_Simp_Result_mkCast___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3___boxed(lean_object**);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1;
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Meta_Simp_withPreservedCache___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object*);
extern lean_object* l_Lean_Meta_simpDtConfig;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed;
static size_t l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4;
static size_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1;
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13;
static size_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2;
static lean_object* l_Lean_Meta_Simp_instInhabitedStats___closed__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStats;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig___boxed(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6;
static lean_object* l_Lean_Meta_Simp_instInhabitedStep___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TransformStep_toStep___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1;
static lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4(lean_object*, lean_object*, size_t, size_t);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Result_mkCast___closed__2;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2___boxed(lean_object**);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1;
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__4;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__3;
static lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4;
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedResult___closed__1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_2 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
if (x_2 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; 
lean_ctor_set(x_3, 1, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_25);
lean_dec(x_3);
if (x_2 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_35 = x_3;
} else {
 lean_dec_ref(x_3);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
if (x_2 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 1);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = l_Lean_Meta_mkEqTrans(x_42, x_47, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_18, 0, x_50);
if (x_2 == 0)
{
uint8_t x_51; 
x_51 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_51);
lean_ctor_set(x_48, 0, x_3);
return x_48;
}
else
{
lean_ctor_set(x_48, 0, x_3);
return x_48;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
lean_ctor_set(x_18, 0, x_52);
if (x_2 == 0)
{
uint8_t x_54; lean_object* x_55; 
x_54 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_18);
lean_free_object(x_3);
lean_dec(x_44);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_18, 0);
lean_inc(x_61);
lean_dec(x_18);
x_62 = l_Lean_Meta_mkEqTrans(x_42, x_61, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
if (x_2 == 0)
{
uint8_t x_67; lean_object* x_68; 
x_67 = 0;
lean_ctor_set(x_3, 1, x_66);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_67);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; 
lean_ctor_set(x_3, 1, x_66);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_3);
lean_dec(x_44);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_74);
lean_dec(x_3);
x_76 = lean_ctor_get(x_18, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_77 = x_18;
} else {
 lean_dec_ref(x_18);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_mkEqTrans(x_42, x_76, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_79);
if (x_2 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_75);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_80);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_77);
lean_dec(x_74);
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_90 = x_78;
} else {
 lean_dec_ref(x_78);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = l_Lean_Meta_mkEqSymm(x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_8, 0, x_23);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_2, 0, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_8);
lean_free_object(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Lean_Meta_mkEqSymm(x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_43 = lean_ctor_get(x_8, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_44 = x_8;
} else {
 lean_dec_ref(x_8);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Meta_mkEqSymm(x_43, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_46);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_42);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_44);
lean_dec(x_1);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 16, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 17, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 18, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__3;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__5;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__9() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__1;
x_4 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
x_5 = l_Lean_Meta_Simp_instInhabitedContext___closed__8;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set_uint32(x_8, sizeof(void*)*5, x_1);
lean_ctor_set_uint32(x_8, sizeof(void*)*5 + 4, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*5 + 8, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__9;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_Context_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_16 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_22 = lean_name_eq(x_18, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_6 = x_23;
goto block_11;
}
else
{
if (x_19 == 0)
{
if (x_21 == 0)
{
uint8_t x_24; 
x_24 = 1;
x_6 = x_24;
goto block_11;
}
else
{
uint8_t x_25; 
x_25 = 0;
x_6 = x_25;
goto block_11;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_26; 
x_26 = 0;
x_6 = x_26;
goto block_11;
}
else
{
uint8_t x_27; 
x_27 = 1;
x_6 = x_27;
goto block_11;
}
}
}
}
else
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_name_eq(x_29, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 0;
x_6 = x_33;
goto block_11;
}
else
{
if (x_30 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_6 = x_34;
goto block_11;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_6 = x_35;
goto block_11;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_name_eq(x_36, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 0;
x_6 = x_40;
goto block_11;
}
else
{
if (x_37 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_6 = x_41;
goto block_11;
}
else
{
uint8_t x_42; 
x_42 = 1;
x_6 = x_42;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_Origin_key(x_5);
x_44 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_6 = x_45;
goto block_11;
}
}
else
{
uint8_t x_46; 
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (x_46 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_51 = lean_name_eq(x_48, x_49);
lean_dec(x_49);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_6 = x_52;
goto block_11;
}
else
{
if (x_50 == 0)
{
uint8_t x_53; 
x_53 = 1;
x_6 = x_53;
goto block_11;
}
else
{
uint8_t x_54; 
x_54 = 0;
x_6 = x_54;
goto block_11;
}
}
}
else
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = lean_ctor_get(x_15, 0);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_name_eq(x_56, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_6 = x_59;
goto block_11;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_6 = x_60;
goto block_11;
}
}
else
{
uint8_t x_61; 
lean_dec(x_15);
x_61 = 0;
x_6 = x_61;
goto block_11;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_15);
x_62 = 0;
x_6 = x_62;
goto block_11;
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = lean_ctor_get(x_15, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_67 = lean_name_eq(x_64, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = 0;
x_6 = x_68;
goto block_11;
}
else
{
if (x_66 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_6 = x_69;
goto block_11;
}
else
{
uint8_t x_70; 
x_70 = 1;
x_6 = x_70;
goto block_11;
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_15);
x_72 = 0;
x_6 = x_72;
goto block_11;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_5, 0);
x_74 = lean_ctor_get(x_15, 0);
lean_inc(x_74);
lean_dec(x_15);
x_75 = lean_name_eq(x_73, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = 0;
x_6 = x_76;
goto block_11;
}
else
{
uint8_t x_77; 
x_77 = 1;
x_6 = x_77;
goto block_11;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_5, 0);
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_46);
lean_ctor_set_uint8(x_79, sizeof(void*)*1 + 1, x_46);
x_80 = l_Lean_Meta_Origin_key(x_79);
lean_dec(x_79);
x_81 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_82 = lean_name_eq(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
x_6 = x_82;
goto block_11;
}
}
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Meta_Origin_key(x_5);
x_85 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_86 = lean_name_eq(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
x_6 = x_86;
goto block_11;
}
else
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
if (x_87 == 0)
{
uint8_t x_88; 
lean_dec(x_15);
x_88 = 0;
x_6 = x_88;
goto block_11;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_15);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_87);
x_90 = l_Lean_Meta_Origin_key(x_5);
x_91 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_92 = lean_name_eq(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
x_6 = x_92;
goto block_11;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_15, 0);
lean_inc(x_93);
lean_dec(x_15);
x_94 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_87);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_87);
x_95 = l_Lean_Meta_Origin_key(x_5);
x_96 = l_Lean_Meta_Origin_key(x_94);
lean_dec(x_94);
x_97 = lean_name_eq(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
x_6 = x_97;
goto block_11;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Meta_Origin_key(x_5);
x_99 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_100 = lean_name_eq(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
x_6 = x_100;
goto block_11;
}
}
}
block_11:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_18 = lean_name_eq(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
else
{
if (x_15 == 0)
{
if (x_17 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
else
{
return x_17;
}
}
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_name_eq(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
else
{
if (x_24 == 0)
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_name_eq(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
else
{
return x_31;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_36 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_37 = lean_name_eq(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
lean_dec(x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_39, sizeof(void*)*1 + 1);
lean_dec(x_39);
x_44 = lean_name_eq(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 0;
return x_45;
}
else
{
if (x_43 == 0)
{
uint8_t x_46; 
x_46 = 1;
return x_46;
}
else
{
uint8_t x_47; 
x_47 = 0;
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = lean_ctor_get_uint8(x_39, sizeof(void*)*1 + 1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_name_eq(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_39);
lean_dec(x_3);
x_52 = 0;
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_39);
lean_dec(x_3);
x_53 = 0;
return x_53;
}
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_10, 0);
lean_inc(x_54);
lean_dec(x_10);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_54, sizeof(void*)*1 + 1);
lean_dec(x_54);
x_59 = lean_name_eq(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
return x_60;
}
else
{
return x_58;
}
}
else
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_54, sizeof(void*)*1 + 1);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_54);
lean_dec(x_3);
x_62 = 0;
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
lean_dec(x_3);
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_name_eq(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_38);
x_67 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_68 = l_Lean_Meta_Origin_key(x_54);
lean_dec(x_54);
x_69 = lean_name_eq(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_38);
lean_ctor_set_uint8(x_71, sizeof(void*)*1 + 1, x_38);
x_72 = l_Lean_Meta_Origin_key(x_71);
lean_dec(x_71);
x_73 = l_Lean_Meta_Origin_key(x_54);
lean_dec(x_54);
x_74 = lean_name_eq(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
return x_74;
}
}
}
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_10, 0);
lean_inc(x_75);
lean_dec(x_10);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_78 = l_Lean_Meta_Origin_key(x_75);
lean_dec(x_75);
x_79 = lean_name_eq(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_ctor_get_uint8(x_75, sizeof(void*)*1 + 1);
if (x_80 == 0)
{
uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_3);
x_81 = 0;
return x_81;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_80);
x_83 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_84 = l_Lean_Meta_Origin_key(x_75);
lean_dec(x_75);
x_85 = lean_name_eq(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_80);
lean_ctor_set_uint8(x_87, sizeof(void*)*1 + 1, x_80);
x_88 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_89 = l_Lean_Meta_Origin_key(x_87);
lean_dec(x_87);
x_90 = lean_name_eq(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_92 = l_Lean_Meta_Origin_key(x_75);
lean_dec(x_75);
x_93 = lean_name_eq(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
return x_93;
}
}
}
case 1:
{
lean_object* x_94; size_t x_95; 
x_94 = lean_ctor_get(x_10, 0);
lean_inc(x_94);
lean_dec(x_10);
x_95 = lean_usize_shift_right(x_2, x_5);
x_1 = x_94;
x_2 = x_95;
goto _start;
}
default: 
{
uint8_t x_97; 
lean_dec(x_3);
x_97 = 0;
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(x_98, x_99, lean_box(0), x_100, x_3);
lean_dec(x_3);
lean_dec(x_99);
lean_dec(x_98);
return x_101;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Name_hash___override(x_4);
lean_dec(x_4);
x_6 = 13;
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(x_1, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = l_Lean_Name_hash___override(x_10);
lean_dec(x_10);
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(x_1, x_14, x_2);
return x_15;
}
}
else
{
lean_object* x_16; uint64_t x_17; size_t x_18; uint8_t x_19; 
x_16 = l_Lean_Meta_Origin_key(x_2);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(x_1, x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*1 + 1);
if (x_17 == 0)
{
lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = 13;
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_shift_right(x_22, x_14);
x_24 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_6, x_23, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = l_Lean_Name_hash___override(x_26);
lean_dec(x_26);
x_28 = 11;
x_29 = lean_uint64_mix_hash(x_27, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_shift_right(x_30, x_14);
x_32 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_6, x_31, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_34 = l_Lean_Meta_Origin_key(x_9);
x_35 = l_Lean_Name_hash___override(x_34);
lean_dec(x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_shift_right(x_36, x_14);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_6, x_37, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_38;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t x_17; lean_object* x_30; 
x_30 = lean_array_fget(x_5, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_31; 
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_31 == 0)
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec(x_30);
x_37 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_17 = x_38;
goto block_29;
}
else
{
if (x_34 == 0)
{
if (x_36 == 0)
{
uint8_t x_39; 
x_39 = 1;
x_17 = x_39;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = 0;
x_17 = x_40;
goto block_29;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_17 = x_41;
goto block_29;
}
else
{
uint8_t x_42; 
x_42 = 1;
x_17 = x_42;
goto block_29;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_name_eq(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = 0;
x_17 = x_48;
goto block_29;
}
else
{
if (x_45 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_17 = x_49;
goto block_29;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_17 = x_50;
goto block_29;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_name_eq(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_17 = x_55;
goto block_29;
}
else
{
if (x_52 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_17 = x_56;
goto block_29;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_17 = x_57;
goto block_29;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Meta_Origin_key(x_3);
x_59 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_60 = lean_name_eq(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
x_17 = x_60;
goto block_29;
}
}
else
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_61 == 0)
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_30, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec(x_30);
x_66 = lean_name_eq(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = 0;
x_17 = x_67;
goto block_29;
}
else
{
if (x_65 == 0)
{
uint8_t x_68; 
x_68 = 1;
x_17 = x_68;
goto block_29;
}
else
{
uint8_t x_69; 
x_69 = 0;
x_17 = x_69;
goto block_29;
}
}
}
else
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_30, 0);
lean_inc(x_72);
lean_dec(x_30);
x_73 = lean_name_eq(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_17 = x_74;
goto block_29;
}
else
{
uint8_t x_75; 
x_75 = 1;
x_17 = x_75;
goto block_29;
}
}
else
{
uint8_t x_76; 
lean_dec(x_30);
x_76 = 0;
x_17 = x_76;
goto block_29;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_30);
x_77 = 0;
x_17 = x_77;
goto block_29;
}
}
else
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_30, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec(x_30);
x_82 = lean_name_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = 0;
x_17 = x_83;
goto block_29;
}
else
{
if (x_81 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_17 = x_84;
goto block_29;
}
else
{
uint8_t x_85; 
x_85 = 1;
x_17 = x_85;
goto block_29;
}
}
}
else
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_30);
x_87 = 0;
x_17 = x_87;
goto block_29;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_30, 0);
lean_inc(x_89);
lean_dec(x_30);
x_90 = lean_name_eq(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_17 = x_91;
goto block_29;
}
else
{
uint8_t x_92; 
x_92 = 1;
x_17 = x_92;
goto block_29;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
x_94 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_61);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_61);
x_95 = l_Lean_Meta_Origin_key(x_94);
lean_dec(x_94);
x_96 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_97 = lean_name_eq(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
x_17 = x_97;
goto block_29;
}
}
}
}
else
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Lean_Meta_Origin_key(x_3);
x_100 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_101 = lean_name_eq(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
x_17 = x_101;
goto block_29;
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_30);
x_103 = 0;
x_17 = x_103;
goto block_29;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_30);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_102);
x_105 = l_Lean_Meta_Origin_key(x_3);
x_106 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_107 = lean_name_eq(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
x_17 = x_107;
goto block_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_30, 0);
lean_inc(x_108);
lean_dec(x_30);
x_109 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_102);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 1, x_102);
x_110 = l_Lean_Meta_Origin_key(x_3);
x_111 = l_Lean_Meta_Origin_key(x_109);
lean_dec(x_109);
x_112 = lean_name_eq(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
x_17 = x_112;
goto block_29;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = l_Lean_Meta_Origin_key(x_3);
x_114 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_115 = lean_name_eq(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
x_17 = x_115;
goto block_29;
}
}
block_29:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = lean_array_fset(x_5, x_2, x_3);
x_27 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_7;
}
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_6, x_12);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_12, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_21 = x_16;
} else {
 lean_dec_ref(x_16);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_31; 
x_31 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_31 == 0)
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_37 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_22 = x_38;
goto block_30;
}
else
{
if (x_34 == 0)
{
if (x_36 == 0)
{
uint8_t x_39; 
x_39 = 1;
x_22 = x_39;
goto block_30;
}
else
{
uint8_t x_40; 
x_40 = 0;
x_22 = x_40;
goto block_30;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_22 = x_41;
goto block_30;
}
else
{
uint8_t x_42; 
x_42 = 1;
x_22 = x_42;
goto block_30;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
x_47 = lean_name_eq(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = 0;
x_22 = x_48;
goto block_30;
}
else
{
if (x_45 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_22 = x_49;
goto block_30;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_22 = x_50;
goto block_30;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
x_54 = lean_name_eq(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_22 = x_55;
goto block_30;
}
else
{
if (x_52 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_22 = x_56;
goto block_30;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_22 = x_57;
goto block_30;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Meta_Origin_key(x_4);
x_59 = l_Lean_Meta_Origin_key(x_19);
x_60 = lean_name_eq(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
x_22 = x_60;
goto block_30;
}
}
else
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
if (x_61 == 0)
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_66 = lean_name_eq(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = 0;
x_22 = x_67;
goto block_30;
}
else
{
if (x_65 == 0)
{
uint8_t x_68; 
x_68 = 1;
x_22 = x_68;
goto block_30;
}
else
{
uint8_t x_69; 
x_69 = 0;
x_22 = x_69;
goto block_30;
}
}
}
else
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_4, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 0);
lean_inc(x_72);
x_73 = lean_name_eq(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_22 = x_74;
goto block_30;
}
else
{
uint8_t x_75; 
x_75 = 1;
x_22 = x_75;
goto block_30;
}
}
else
{
uint8_t x_76; 
x_76 = 0;
x_22 = x_76;
goto block_30;
}
}
}
else
{
uint8_t x_77; 
x_77 = 0;
x_22 = x_77;
goto block_30;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_19, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_82 = lean_name_eq(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = 0;
x_22 = x_83;
goto block_30;
}
else
{
if (x_81 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_22 = x_84;
goto block_30;
}
else
{
uint8_t x_85; 
x_85 = 1;
x_22 = x_85;
goto block_30;
}
}
}
else
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = 0;
x_22 = x_87;
goto block_30;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_4, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_19, 0);
lean_inc(x_89);
x_90 = lean_name_eq(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_22 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
x_92 = 1;
x_22 = x_92;
goto block_30;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_4, 0);
lean_inc(x_93);
x_94 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_61);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_61);
x_95 = l_Lean_Meta_Origin_key(x_94);
lean_dec(x_94);
x_96 = l_Lean_Meta_Origin_key(x_19);
x_97 = lean_name_eq(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
x_22 = x_97;
goto block_30;
}
}
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Lean_Meta_Origin_key(x_4);
x_100 = l_Lean_Meta_Origin_key(x_19);
x_101 = lean_name_eq(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
x_22 = x_101;
goto block_30;
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = 0;
x_22 = x_103;
goto block_30;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_19, 0);
lean_inc(x_104);
x_105 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_102);
lean_ctor_set_uint8(x_105, sizeof(void*)*1 + 1, x_102);
x_106 = l_Lean_Meta_Origin_key(x_4);
x_107 = l_Lean_Meta_Origin_key(x_105);
lean_dec(x_105);
x_108 = lean_name_eq(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
x_22 = x_108;
goto block_30;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = l_Lean_Meta_Origin_key(x_4);
x_110 = l_Lean_Meta_Origin_key(x_19);
x_111 = lean_name_eq(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
x_22 = x_111;
goto block_30;
}
}
block_30:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_23 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_array_fset(x_18, x_12, x_24);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_7;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_19);
if (lean_is_scalar(x_21)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_21;
}
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
x_28 = lean_array_fset(x_18, x_12, x_27);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_7;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
case 1:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_16);
if (x_112 == 0)
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_16, 0);
x_114 = lean_usize_shift_right(x_2, x_9);
x_115 = lean_usize_add(x_3, x_8);
x_116 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_113, x_114, x_115, x_4, x_5);
lean_ctor_set(x_16, 0, x_116);
x_117 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_118 = lean_alloc_ctor(0, 1, 0);
} else {
 x_118 = x_7;
}
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
else
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_16, 0);
lean_inc(x_119);
lean_dec(x_16);
x_120 = lean_usize_shift_right(x_2, x_9);
x_121 = lean_usize_add(x_3, x_8);
x_122 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_119, x_120, x_121, x_4, x_5);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_array_fset(x_18, x_12, x_123);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_4);
lean_ctor_set(x_126, 1, x_5);
x_127 = lean_array_fset(x_18, x_12, x_126);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_128 = lean_alloc_ctor(0, 1, 0);
} else {
 x_128 = x_7;
}
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_1);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; size_t x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(x_1, x_130, x_4, x_5);
x_132 = 7;
x_133 = lean_usize_dec_le(x_132, x_3);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_131);
x_135 = lean_unsigned_to_nat(4u);
x_136 = lean_nat_dec_lt(x_134, x_135);
lean_dec(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
lean_dec(x_131);
x_139 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
x_140 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(x_3, x_137, x_138, lean_box(0), x_130, x_139);
lean_dec(x_138);
lean_dec(x_137);
return x_140;
}
else
{
return x_131;
}
}
else
{
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; uint8_t x_147; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_1);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(x_143, x_144, x_4, x_5);
x_146 = 7;
x_147 = lean_usize_dec_le(x_146, x_3);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_145);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_nat_dec_lt(x_148, x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_dec(x_145);
x_153 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
x_154 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(x_3, x_151, x_152, lean_box(0), x_144, x_153);
lean_dec(x_152);
lean_dec(x_151);
return x_154;
}
else
{
return x_145;
}
}
else
{
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; 
x_4 = 1;
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = 13;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_1, x_10, x_4, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lean_Name_hash___override(x_12);
lean_dec(x_12);
x_14 = 11;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_1, x_16, x_4, x_2, x_3);
return x_17;
}
}
else
{
lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; 
x_18 = l_Lean_Meta_Origin_key(x_2);
x_19 = l_Lean_Name_hash___override(x_18);
lean_dec(x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_1, x_20, x_4, x_2, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_6, x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_11, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2;
x_3 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_3, x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_size(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(x_9, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_UsedSimps_toArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1;
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_2 = l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1;
x_2 = l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedStats___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_dsimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 4);
x_25 = lean_apply_1(x_1, x_24);
lean_ctor_set(x_21, 4, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_38 = lean_apply_1(x_1, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_ref_set(x_4, x_39, x_22);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_modifyDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedStep___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_TransformStep_toStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = 1;
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
default: 
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_free_object(x_1);
x_24 = l_Lean_TransformStep_toStep___closed__1;
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_box(0);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
lean_ctor_set(x_23, 0, x_29);
return x_1;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = l_Lean_TransformStep_toStep___closed__1;
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
x_40 = 1;
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_25 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_39 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_37, x_38, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set(x_39, 0, x_2);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_2, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_2);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_52 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_50, x_51, x_49, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
default: 
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_2, 0, x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_70 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_68, x_69, x_67, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set(x_63, 0, x_72);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_70);
lean_ctor_set(x_63, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_free_object(x_63);
lean_free_object(x_2);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_63, 0);
lean_inc(x_80);
lean_dec(x_63);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_83 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_81, x_82, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_2, 0, x_87);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_2);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_2, 0);
lean_inc(x_93);
lean_dec(x_2);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_98 = x_93;
} else {
 lean_dec_ref(x_93);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_101 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_99, x_100, x_97, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_98;
}
lean_ctor_set(x_105, 0, x_102);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_21 = x_13;
} else {
 lean_dec_ref(x_13);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_31 = x_13;
} else {
 lean_dec_ref(x_13);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
default: 
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = lean_apply_9(x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Simp_mkEqTransResultStep(x_38, x_41, x_7, x_8, x_9, x_10, x_42);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
return x_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_12);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = l_Lean_Meta_Simp_andThen(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_21 = x_13;
} else {
 lean_dec_ref(x_13);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_31 = x_13;
} else {
 lean_dec_ref(x_13);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
default: 
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_apply_9(x_2, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = l_Lean_Meta_Simp_dandThen(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_instInhabitedStep___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lambda__3___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
x_2 = l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
x_3 = l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getMethods(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getContext___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getContext___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getContext(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getConfig___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getConfig___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 3);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_4, 3, x_13);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*5);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get_uint32(x_4, sizeof(void*)*5 + 4);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 8);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set_uint32(x_23, sizeof(void*)*5, x_16);
lean_ctor_set_uint32(x_23, sizeof(void*)*5 + 4, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 8, x_21);
x_24 = lean_apply_8(x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withParent___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getSimpTheorems___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSimpTheorems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSimpCongrTheorems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 8);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_inDSimp___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_inDSimp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_inDSimp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Meta_Simp_withPreservedCache___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_4, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_4, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_Lean_SMap_switch___at_Lean_Meta_Simp_withPreservedCache___spec__1(x_24);
lean_ctor_set(x_21, 0, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_4);
x_28 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_take(x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_dec(x_38);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_19);
x_39 = lean_st_ref_set(x_4, x_32, x_34);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_29);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_14);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_19);
lean_ctor_set(x_32, 0, x_45);
x_46 = lean_st_ref_set(x_4, x_32, x_34);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_32, 1);
x_51 = lean_ctor_get(x_32, 2);
x_52 = lean_ctor_get(x_32, 3);
x_53 = lean_ctor_get(x_32, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_32);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_55 = x_33;
} else {
 lean_dec_ref(x_33);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_14);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_19);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_57, 3, x_52);
lean_ctor_set(x_57, 4, x_53);
x_58 = lean_st_ref_set(x_4, x_57, x_34);
lean_dec(x_4);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_28, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_st_ref_take(x_4, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_dec(x_71);
lean_ctor_set(x_66, 1, x_14);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_19);
x_72 = lean_st_ref_set(x_4, x_65, x_67);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_62);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_62);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_19);
lean_ctor_set(x_65, 0, x_78);
x_79 = lean_st_ref_set(x_4, x_65, x_67);
lean_dec(x_4);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_83 = lean_ctor_get(x_65, 1);
x_84 = lean_ctor_get(x_65, 2);
x_85 = lean_ctor_get(x_65, 3);
x_86 = lean_ctor_get(x_65, 4);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_65);
x_87 = lean_ctor_get(x_66, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_88 = x_66;
} else {
 lean_dec_ref(x_66);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 1);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_14);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_19);
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_85);
lean_ctor_set(x_90, 4, x_86);
x_91 = lean_st_ref_set(x_4, x_90, x_67);
lean_dec(x_4);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_62);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
x_97 = lean_ctor_get(x_21, 2);
x_98 = lean_ctor_get(x_21, 3);
x_99 = lean_ctor_get(x_21, 4);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_100 = l_Lean_SMap_switch___at_Lean_Meta_Simp_withPreservedCache___spec__1(x_95);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
lean_ctor_set(x_101, 2, x_97);
lean_ctor_set(x_101, 3, x_98);
lean_ctor_set(x_101, 4, x_99);
x_102 = lean_st_ref_set(x_4, x_101, x_22);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_4);
x_104 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_take(x_4, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_14);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_19);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(0, 5, 0);
} else {
 x_119 = x_115;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_112);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set(x_119, 4, x_114);
x_120 = lean_st_ref_set(x_4, x_119, x_110);
lean_dec(x_4);
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
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_124 = lean_ctor_get(x_104, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_104, 1);
lean_inc(x_125);
lean_dec(x_104);
x_126 = lean_st_ref_take(x_4, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 4);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 1);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_14);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_19);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 5, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
lean_ctor_set(x_138, 2, x_131);
lean_ctor_set(x_138, 3, x_132);
lean_ctor_set(x_138, 4, x_133);
x_139 = lean_st_ref_set(x_4, x_138, x_129);
lean_dec(x_4);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_124);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withPreservedCache___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_withFreshCache___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__5;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_4, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
lean_ctor_set(x_15, 0, x_19);
x_20 = lean_st_ref_set(x_4, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_4);
x_22 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_take(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
lean_ctor_set(x_26, 0, x_13);
x_30 = lean_st_ref_set(x_4, x_26, x_27);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 3);
x_38 = lean_ctor_get(x_26, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_ref_set(x_4, x_39, x_27);
lean_dec(x_4);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_22, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_dec(x_22);
x_46 = lean_st_ref_take(x_4, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
lean_ctor_set(x_47, 0, x_13);
x_51 = lean_st_ref_set(x_4, x_47, x_48);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_44);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_47, 1);
x_57 = lean_ctor_get(x_47, 2);
x_58 = lean_ctor_get(x_47, 3);
x_59 = lean_ctor_get(x_47, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
x_61 = lean_st_ref_set(x_4, x_60, x_48);
lean_dec(x_4);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_44);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_15, 1);
x_66 = lean_ctor_get(x_15, 2);
x_67 = lean_ctor_get(x_15, 3);
x_68 = lean_ctor_get(x_15, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_69 = l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
x_71 = lean_st_ref_set(x_4, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
lean_inc(x_4);
x_73 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_4, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_13);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
x_85 = lean_st_ref_set(x_4, x_84, x_78);
lean_dec(x_4);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_73, 1);
lean_inc(x_90);
lean_dec(x_73);
x_91 = lean_st_ref_take(x_4, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 4);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_13);
lean_ctor_set(x_99, 1, x_94);
lean_ctor_set(x_99, 2, x_95);
lean_ctor_set(x_99, 3, x_96);
lean_ctor_set(x_99, 4, x_97);
x_100 = lean_st_ref_set(x_4, x_99, x_93);
lean_dec(x_4);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
 lean_ctor_set_tag(x_103, 1);
}
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withFreshCache___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
lean_ctor_set(x_17, 0, x_21);
x_22 = lean_st_ref_set(x_6, x_17, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 4);
lean_dec(x_25);
lean_ctor_set(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_26 = lean_apply_8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_6, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_15);
x_34 = lean_st_ref_set(x_6, x_30, x_31);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_27);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 1);
x_40 = lean_ctor_get(x_30, 2);
x_41 = lean_ctor_get(x_30, 3);
x_42 = lean_ctor_get(x_30, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_st_ref_set(x_6, x_43, x_31);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_dec(x_26);
x_50 = lean_st_ref_take(x_6, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
lean_ctor_set(x_51, 0, x_15);
x_55 = lean_st_ref_set(x_6, x_51, x_52);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 0, x_48);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 2);
x_62 = lean_ctor_get(x_51, 3);
x_63 = lean_ctor_get(x_51, 4);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_63);
x_65 = lean_st_ref_set(x_6, x_64, x_52);
lean_dec(x_6);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_48);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_4, 0);
x_70 = lean_ctor_get(x_4, 1);
x_71 = lean_ctor_get(x_4, 2);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_1);
lean_ctor_set_uint8(x_73, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_74 = lean_apply_8(x_3, x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_st_ref_take(x_6, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_15);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
x_86 = lean_st_ref_set(x_6, x_85, x_79);
lean_dec(x_6);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_75);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
lean_dec(x_74);
x_92 = lean_st_ref_take(x_6, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 4);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_96);
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set(x_100, 4, x_98);
x_101 = lean_st_ref_set(x_6, x_100, x_94);
lean_dec(x_6);
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
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
 lean_ctor_set_tag(x_104, 1);
}
lean_ctor_set(x_104, 0, x_90);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_105 = lean_ctor_get(x_17, 1);
x_106 = lean_ctor_get(x_17, 2);
x_107 = lean_ctor_get(x_17, 3);
x_108 = lean_ctor_get(x_17, 4);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_17);
x_109 = l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
lean_ctor_set(x_110, 2, x_106);
lean_ctor_set(x_110, 3, x_107);
lean_ctor_set(x_110, 4, x_108);
x_111 = lean_st_ref_set(x_6, x_110, x_18);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_4, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_117 = x_4;
} else {
 lean_dec_ref(x_4);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 5, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_1);
lean_ctor_set_uint8(x_118, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_119 = lean_apply_8(x_3, x_118, x_5, x_6, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_st_ref_take(x_6, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 4);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_15);
lean_ctor_set(x_130, 1, x_125);
lean_ctor_set(x_130, 2, x_126);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set(x_130, 4, x_128);
x_131 = lean_st_ref_set(x_6, x_130, x_124);
lean_dec(x_6);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_120);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_119, 1);
lean_inc(x_136);
lean_dec(x_119);
x_137 = lean_st_ref_take(x_6, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_138, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 4);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_15);
lean_ctor_set(x_145, 1, x_140);
lean_ctor_set(x_145, 2, x_141);
lean_ctor_set(x_145, 3, x_142);
lean_ctor_set(x_145, 4, x_143);
x_146 = lean_st_ref_set(x_6, x_145, x_139);
lean_dec(x_6);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
 lean_ctor_set_tag(x_149, 1);
}
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withDischarger___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Simp_withDischarger___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fget(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_17 == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_23 = lean_name_eq(x_19, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_6 = x_24;
goto block_12;
}
else
{
if (x_20 == 0)
{
if (x_22 == 0)
{
uint8_t x_25; 
x_25 = 1;
x_6 = x_25;
goto block_12;
}
else
{
uint8_t x_26; 
x_26 = 0;
x_6 = x_26;
goto block_12;
}
}
else
{
if (x_22 == 0)
{
uint8_t x_27; 
x_27 = 0;
x_6 = x_27;
goto block_12;
}
else
{
uint8_t x_28; 
x_28 = 1;
x_6 = x_28;
goto block_12;
}
}
}
}
else
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_name_eq(x_30, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 0;
x_6 = x_34;
goto block_12;
}
else
{
if (x_31 == 0)
{
uint8_t x_35; 
x_35 = 1;
x_6 = x_35;
goto block_12;
}
else
{
uint8_t x_36; 
x_36 = 0;
x_6 = x_36;
goto block_12;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_name_eq(x_37, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 0;
x_6 = x_41;
goto block_12;
}
else
{
if (x_38 == 0)
{
uint8_t x_42; 
x_42 = 0;
x_6 = x_42;
goto block_12;
}
else
{
uint8_t x_43; 
x_43 = 1;
x_6 = x_43;
goto block_12;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Meta_Origin_key(x_5);
x_45 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_46 = lean_name_eq(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
x_6 = x_46;
goto block_12;
}
}
else
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
if (x_47 == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_48; 
x_48 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_ctor_get(x_16, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_52 = lean_name_eq(x_49, x_50);
lean_dec(x_50);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_6 = x_53;
goto block_12;
}
else
{
if (x_51 == 0)
{
uint8_t x_54; 
x_54 = 1;
x_6 = x_54;
goto block_12;
}
else
{
uint8_t x_55; 
x_55 = 0;
x_6 = x_55;
goto block_12;
}
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_16, 0);
lean_inc(x_58);
lean_dec(x_16);
x_59 = lean_name_eq(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
x_6 = x_60;
goto block_12;
}
else
{
uint8_t x_61; 
x_61 = 1;
x_6 = x_61;
goto block_12;
}
}
else
{
uint8_t x_62; 
lean_dec(x_16);
x_62 = 0;
x_6 = x_62;
goto block_12;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_16);
x_63 = 0;
x_6 = x_63;
goto block_12;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_5, 0);
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_68 = lean_name_eq(x_65, x_66);
lean_dec(x_66);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_6 = x_69;
goto block_12;
}
else
{
if (x_67 == 0)
{
uint8_t x_70; 
x_70 = 0;
x_6 = x_70;
goto block_12;
}
else
{
uint8_t x_71; 
x_71 = 1;
x_6 = x_71;
goto block_12;
}
}
}
else
{
uint8_t x_72; 
x_72 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_16);
x_73 = 0;
x_6 = x_73;
goto block_12;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_16, 0);
lean_inc(x_75);
lean_dec(x_16);
x_76 = lean_name_eq(x_74, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
x_6 = x_77;
goto block_12;
}
else
{
uint8_t x_78; 
x_78 = 1;
x_6 = x_78;
goto block_12;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_47);
lean_ctor_set_uint8(x_80, sizeof(void*)*1 + 1, x_47);
x_81 = l_Lean_Meta_Origin_key(x_80);
lean_dec(x_80);
x_82 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_83 = lean_name_eq(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
x_6 = x_83;
goto block_12;
}
}
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_84; 
x_84 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = l_Lean_Meta_Origin_key(x_5);
x_86 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_87 = lean_name_eq(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
x_6 = x_87;
goto block_12;
}
else
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_16);
x_89 = 0;
x_6 = x_89;
goto block_12;
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_16);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_88);
x_91 = l_Lean_Meta_Origin_key(x_5);
x_92 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_93 = lean_name_eq(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
x_6 = x_93;
goto block_12;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_16, 0);
lean_inc(x_94);
lean_dec(x_16);
x_95 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_88);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 1, x_88);
x_96 = l_Lean_Meta_Origin_key(x_5);
x_97 = l_Lean_Meta_Origin_key(x_95);
lean_dec(x_95);
x_98 = lean_name_eq(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
x_6 = x_98;
goto block_12;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Lean_Meta_Origin_key(x_5);
x_100 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_101 = lean_name_eq(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
x_6 = x_101;
goto block_12;
}
}
}
block_12:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_18 == 0)
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_24 = lean_name_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
x_14 = x_25;
goto block_17;
}
else
{
if (x_21 == 0)
{
if (x_23 == 0)
{
uint8_t x_26; 
x_26 = 1;
x_14 = x_26;
goto block_17;
}
else
{
uint8_t x_27; 
x_27 = 0;
x_14 = x_27;
goto block_17;
}
}
else
{
if (x_23 == 0)
{
uint8_t x_28; 
x_28 = 0;
x_14 = x_28;
goto block_17;
}
else
{
uint8_t x_29; 
x_29 = 1;
x_14 = x_29;
goto block_17;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_name_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 0;
x_14 = x_35;
goto block_17;
}
else
{
if (x_32 == 0)
{
uint8_t x_36; 
x_36 = 1;
x_14 = x_36;
goto block_17;
}
else
{
uint8_t x_37; 
x_37 = 0;
x_14 = x_37;
goto block_17;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
lean_dec(x_3);
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_name_eq(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
x_14 = x_42;
goto block_17;
}
else
{
if (x_39 == 0)
{
uint8_t x_43; 
x_43 = 0;
x_14 = x_43;
goto block_17;
}
else
{
uint8_t x_44; 
x_44 = 1;
x_14 = x_44;
goto block_17;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_46 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_47 = lean_name_eq(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_14 = x_47;
goto block_17;
}
}
else
{
uint8_t x_48; 
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_48 == 0)
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_53 = lean_name_eq(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = 0;
x_14 = x_54;
goto block_17;
}
else
{
if (x_52 == 0)
{
uint8_t x_55; 
x_55 = 1;
x_14 = x_55;
goto block_17;
}
else
{
uint8_t x_56; 
x_56 = 0;
x_14 = x_56;
goto block_17;
}
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
lean_dec(x_3);
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_name_eq(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = 0;
x_14 = x_61;
goto block_17;
}
else
{
uint8_t x_62; 
x_62 = 1;
x_14 = x_62;
goto block_17;
}
}
else
{
uint8_t x_63; 
lean_dec(x_12);
lean_dec(x_3);
x_63 = 0;
x_14 = x_63;
goto block_17;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_3);
x_64 = 0;
x_14 = x_64;
goto block_17;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_65; 
x_65 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
lean_dec(x_3);
x_67 = lean_ctor_get(x_12, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_69 = lean_name_eq(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
x_14 = x_70;
goto block_17;
}
else
{
if (x_68 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_14 = x_71;
goto block_17;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_14 = x_72;
goto block_17;
}
}
}
else
{
uint8_t x_73; 
x_73 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_3);
x_74 = 0;
x_14 = x_74;
goto block_17;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
lean_dec(x_3);
x_76 = lean_ctor_get(x_12, 0);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_name_eq(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_14 = x_78;
goto block_17;
}
else
{
uint8_t x_79; 
x_79 = 1;
x_14 = x_79;
goto block_17;
}
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_3);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_48);
x_81 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_82 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_83 = lean_name_eq(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
x_14 = x_83;
goto block_17;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_3, 0);
lean_inc(x_84);
lean_dec(x_3);
x_85 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_85, sizeof(void*)*1 + 1, x_48);
x_86 = l_Lean_Meta_Origin_key(x_85);
lean_dec(x_85);
x_87 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_88 = lean_name_eq(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_14 = x_88;
goto block_17;
}
}
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_91 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_92 = lean_name_eq(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
x_14 = x_92;
goto block_17;
}
else
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_12);
lean_dec(x_3);
x_94 = 0;
x_14 = x_94;
goto block_17;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_93);
x_96 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_97 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_98 = lean_name_eq(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
x_14 = x_98;
goto block_17;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_12, 0);
lean_inc(x_99);
lean_dec(x_12);
x_100 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_93);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 1, x_93);
x_101 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_102 = l_Lean_Meta_Origin_key(x_100);
lean_dec(x_100);
x_103 = lean_name_eq(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
x_14 = x_103;
goto block_17;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Lean_Meta_Origin_key(x_3);
lean_dec(x_3);
x_105 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_106 = lean_name_eq(x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
x_14 = x_106;
goto block_17;
}
}
block_17:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_5);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
if (lean_is_scalar(x_5)) {
 x_16 = lean_alloc_ctor(1, 1, 0);
} else {
 x_16 = x_5;
 lean_ctor_set_tag(x_16, 1);
}
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
}
case 1:
{
lean_object* x_107; size_t x_108; 
lean_dec(x_5);
x_107 = lean_ctor_get(x_11, 0);
lean_inc(x_107);
lean_dec(x_11);
x_108 = lean_usize_shift_right(x_2, x_6);
x_1 = x_107;
x_2 = x_108;
goto _start;
}
default: 
{
lean_object* x_110; 
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_box(0);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(x_111, x_112, lean_box(0), x_113, x_3);
lean_dec(x_3);
lean_dec(x_112);
lean_dec(x_111);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_3 == 0)
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Name_hash___override(x_4);
lean_dec(x_4);
x_6 = 13;
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(x_1, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = l_Lean_Name_hash___override(x_10);
lean_dec(x_10);
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(x_1, x_14, x_2);
return x_15;
}
}
else
{
lean_object* x_16; uint64_t x_17; size_t x_18; lean_object* x_19; 
x_16 = l_Lean_Meta_Origin_key(x_2);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(x_1, x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 4);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_1);
lean_inc(x_27);
x_28 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_27, x_1, x_29);
lean_ctor_set(x_22, 1, x_30);
x_31 = lean_st_ref_set(x_4, x_21, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_27, x_1, x_40);
lean_ctor_set(x_22, 1, x_41);
x_42 = lean_st_ref_set(x_4, x_21, x_23);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
x_51 = lean_ctor_get(x_22, 2);
x_52 = lean_ctor_get(x_22, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
lean_inc(x_1);
lean_inc(x_50);
x_53 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_50, x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_50, x_1, x_54);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_21, 4, x_56);
x_57 = lean_st_ref_set(x_4, x_21, x_23);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_62);
x_65 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_50, x_1, x_64);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_51);
lean_ctor_set(x_66, 3, x_52);
lean_ctor_set(x_21, 4, x_66);
x_67 = lean_st_ref_set(x_4, x_21, x_23);
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
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
x_74 = lean_ctor_get(x_21, 2);
x_75 = lean_ctor_get(x_21, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_22, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_22, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 x_80 = x_22;
} else {
 lean_dec_ref(x_22);
 x_80 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_77);
x_81 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_77, x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_77, x_1, x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 4, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_79);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_73);
lean_ctor_set(x_85, 2, x_74);
lean_ctor_set(x_85, 3, x_75);
lean_ctor_set(x_85, 4, x_84);
x_86 = lean_st_ref_set(x_4, x_85, x_23);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_91);
x_94 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_77, x_1, x_93);
if (lean_is_scalar(x_80)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_80;
}
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_78);
lean_ctor_set(x_95, 3, x_79);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_72);
lean_ctor_set(x_96, 1, x_73);
lean_ctor_set(x_96, 2, x_74);
lean_ctor_set(x_96, 3, x_75);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_st_ref_set(x_4, x_96, x_23);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTriedSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Meta_Simp_UsedSimps_insert(x_14, x_1);
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_28 = l_Lean_Meta_Simp_UsedSimps_insert(x_25, x_1);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
x_30 = lean_st_ref_set(x_4, x_29, x_12);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_recordSimpTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_recordSimpTheorem___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_10 = x_36;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_st_ref_take(x_4, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 4);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_1);
lean_inc(x_45);
x_46 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_45, x_1);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_48 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_45, x_1, x_47);
lean_ctor_set(x_40, 0, x_48);
x_49 = lean_st_ref_set(x_4, x_39, x_41);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_10 = x_50;
goto block_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_51, x_52);
lean_dec(x_51);
lean_inc(x_1);
x_54 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_45, x_1, x_53);
lean_ctor_set(x_40, 0, x_54);
x_55 = lean_st_ref_set(x_4, x_39, x_41);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_10 = x_56;
goto block_32;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_40, 0);
x_58 = lean_ctor_get(x_40, 1);
x_59 = lean_ctor_get(x_40, 2);
x_60 = lean_ctor_get(x_40, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_40);
lean_inc(x_1);
lean_inc(x_57);
x_61 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_57, x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_63 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_57, x_1, x_62);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set(x_39, 4, x_64);
x_65 = lean_st_ref_set(x_4, x_39, x_41);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_10 = x_66;
goto block_32;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_67, x_68);
lean_dec(x_67);
lean_inc(x_1);
x_70 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_57, x_1, x_69);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_58);
lean_ctor_set(x_71, 2, x_59);
lean_ctor_set(x_71, 3, x_60);
lean_ctor_set(x_39, 4, x_71);
x_72 = lean_st_ref_set(x_4, x_39, x_41);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_10 = x_73;
goto block_32;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
x_76 = lean_ctor_get(x_39, 2);
x_77 = lean_ctor_get(x_39, 3);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_78 = lean_ctor_get(x_40, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_82 = x_40;
} else {
 lean_dec_ref(x_40);
 x_82 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_78);
x_83 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_78, x_1);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_85 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_78, x_1, x_84);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 4, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_80);
lean_ctor_set(x_86, 3, x_81);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_75);
lean_ctor_set(x_87, 2, x_76);
lean_ctor_set(x_87, 3, x_77);
lean_ctor_set(x_87, 4, x_86);
x_88 = lean_st_ref_set(x_4, x_87, x_41);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_10 = x_89;
goto block_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
lean_dec(x_83);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_90, x_91);
lean_dec(x_90);
lean_inc(x_1);
x_93 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(x_78, x_1, x_92);
if (lean_is_scalar(x_82)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_82;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_79);
lean_ctor_set(x_94, 2, x_80);
lean_ctor_set(x_94, 3, x_81);
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_74);
lean_ctor_set(x_95, 1, x_75);
lean_ctor_set(x_95, 2, x_76);
lean_ctor_set(x_95, 3, x_77);
lean_ctor_set(x_95, 4, x_94);
x_96 = lean_st_ref_set(x_4, x_95, x_41);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_10 = x_97;
goto block_32;
}
}
}
block_32:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_recordSimpTheorem___closed__1;
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_15 = l_Lean_Meta_isEqnThm_x3f(x_13, x_7, x_8, x_10);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_9(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = 0;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 1, x_23);
x_24 = lean_apply_9(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 1, x_27);
x_29 = lean_apply_9(x_11, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_29;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_apply_9(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_apply_9(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 4);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
x_28 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_27, x_1, x_29);
lean_ctor_set(x_22, 2, x_30);
x_31 = lean_st_ref_set(x_4, x_21, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_27, x_1, x_40);
lean_ctor_set(x_22, 2, x_41);
x_42 = lean_st_ref_set(x_4, x_21, x_23);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
x_51 = lean_ctor_get(x_22, 2);
x_52 = lean_ctor_get(x_22, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
lean_inc(x_51);
x_53 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(x_51, x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_51, x_1, x_54);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_21, 4, x_56);
x_57 = lean_st_ref_set(x_4, x_21, x_23);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_62);
x_65 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_51, x_1, x_64);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_52);
lean_ctor_set(x_21, 4, x_66);
x_67 = lean_st_ref_set(x_4, x_21, x_23);
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
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
x_74 = lean_ctor_get(x_21, 2);
x_75 = lean_ctor_get(x_21, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_22, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_22, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 x_80 = x_22;
} else {
 lean_dec_ref(x_22);
 x_80 = lean_box(0);
}
lean_inc(x_78);
x_81 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Diagnostics_recordUnfold___spec__1(x_78, x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_78, x_1, x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 4, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_79);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_73);
lean_ctor_set(x_85, 2, x_74);
lean_ctor_set(x_85, 3, x_75);
lean_ctor_set(x_85, 4, x_84);
x_86 = lean_st_ref_set(x_4, x_85, x_23);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_91, x_92);
lean_dec(x_91);
x_94 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_78, x_1, x_93);
if (lean_is_scalar(x_80)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_80;
}
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_77);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_79);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_72);
lean_ctor_set(x_96, 1, x_73);
lean_ctor_set(x_96, 2, x_74);
lean_ctor_set(x_96, 3, x_75);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_st_ref_set(x_4, x_96, x_23);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordCongrTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3(x_1, x_3, x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 0;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4(x_1, x_11, x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5(x_1, x_5, x_10, x_11);
return x_12;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 4);
x_25 = l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_PersistentArray_push___rarg(x_27, x_1);
lean_ctor_set(x_24, 3, x_28);
x_29 = lean_st_ref_set(x_4, x_21, x_22);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_40 = l_Lean_PersistentArray_push___rarg(x_39, x_1);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_21, 4, x_41);
x_42 = lean_st_ref_set(x_4, x_21, x_22);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_47 = lean_st_ref_set(x_4, x_21, x_22);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
x_56 = lean_ctor_get(x_21, 2);
x_57 = lean_ctor_get(x_21, 3);
x_58 = lean_ctor_get(x_21, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_59 = l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 3);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
x_65 = l_Lean_PersistentArray_push___rarg(x_63, x_1);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 4, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_54);
lean_ctor_set(x_67, 1, x_55);
lean_ctor_set(x_67, 2, x_56);
lean_ctor_set(x_67, 3, x_57);
lean_ctor_set(x_67, 4, x_66);
x_68 = lean_st_ref_set(x_4, x_67, x_22);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_54);
lean_ctor_set(x_73, 1, x_55);
lean_ctor_set(x_73, 2, x_56);
lean_ctor_set(x_73, 3, x_57);
lean_ctor_set(x_73, 4, x_58);
x_74 = lean_st_ref_set(x_4, x_73, x_22);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTheoremWithBadKeys(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_mkEqRefl(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_Meta_isExprDefEq(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_mkEq(x_1, x_9, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkExpectedTypeHint(x_15, x_18, x_3, x_4, x_5, x_6, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Result_mkCast___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Result_mkCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Result_mkCast___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = l_Lean_Meta_Simp_Result_mkCast___closed__2;
x_16 = l_Lean_Meta_mkAppM(x_15, x_14, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Expr_app___override(x_9, x_2);
x_11 = lean_box(0);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkCongrFun(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Expr_app___override(x_20, x_2);
lean_ctor_set(x_8, 0, x_19);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Expr_app___override(x_26, x_2);
lean_ctor_set(x_8, 0, x_24);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_8);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
lean_inc(x_2);
x_36 = l_Lean_Meta_mkCongrFun(x_35, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lean_Expr_app___override(x_40, x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_43 = 1;
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_43);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_39;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_48 = x_36;
} else {
 lean_dec_ref(x_36);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Expr_app___override(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_mkCongrArg(x_8, x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_12, 0, x_21);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_12);
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_Meta_mkCongrArg(x_8, x_33, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_39);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_8);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_dec(x_2);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = l_Lean_Meta_mkCongrFun(x_48, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_11, 0, x_51);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_10);
lean_ctor_set(x_53, 1, x_11);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_52);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
lean_ctor_set(x_11, 0, x_54);
x_56 = 1;
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_11);
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_11, 0);
lean_inc(x_63);
lean_dec(x_11);
x_64 = l_Lean_Meta_mkCongrFun(x_63, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_69 = 1;
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_69);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_74 = x_64;
} else {
 lean_dec_ref(x_64);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_9);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
lean_dec(x_11);
x_77 = !lean_is_exclusive(x_46);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_46, 0);
x_79 = l_Lean_Meta_mkCongr(x_76, x_78, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
lean_ctor_set(x_46, 0, x_81);
x_82 = 1;
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_46);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_82);
lean_ctor_set(x_79, 0, x_83);
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
lean_ctor_set(x_46, 0, x_84);
x_86 = 1;
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_10);
lean_ctor_set(x_87, 1, x_46);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_free_object(x_46);
lean_dec(x_10);
x_89 = !lean_is_exclusive(x_79);
if (x_89 == 0)
{
return x_79;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_79, 0);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_79);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_46, 0);
lean_inc(x_93);
lean_dec(x_46);
x_94 = l_Lean_Meta_mkCongr(x_76, x_93, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_99 = 1;
x_100 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_100, 0, x_10);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_99);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
x_102 = lean_ctor_get(x_94, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_104 = x_94;
} else {
 lean_dec_ref(x_94);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.updateForallE!", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall expected", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_mkImpCongr___closed__1;
x_2 = l_Lean_Meta_Simp_mkImpCongr___closed__2;
x_3 = lean_unsigned_to_nat(1761u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Meta_Simp_mkImpCongr___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; size_t x_136; size_t x_137; uint8_t x_138; 
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 2);
lean_inc(x_133);
x_134 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
x_135 = l_Lean_Expr_forallE___override(x_131, x_132, x_133, x_134);
x_136 = lean_ptr_addr(x_132);
lean_dec(x_132);
x_137 = lean_ptr_addr(x_9);
x_138 = lean_usize_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_135);
lean_dec(x_133);
x_139 = l_Lean_Expr_forallE___override(x_131, x_9, x_10, x_134);
x_12 = x_139;
goto block_130;
}
else
{
size_t x_140; size_t x_141; uint8_t x_142; 
x_140 = lean_ptr_addr(x_133);
lean_dec(x_133);
x_141 = lean_ptr_addr(x_10);
x_142 = lean_usize_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_135);
x_143 = l_Lean_Expr_forallE___override(x_131, x_9, x_10, x_134);
x_12 = x_143;
goto block_130;
}
else
{
uint8_t x_144; 
x_144 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_134, x_134);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_135);
x_145 = l_Lean_Expr_forallE___override(x_131, x_9, x_10, x_134);
x_12 = x_145;
goto block_130;
}
else
{
lean_dec(x_131);
lean_dec(x_10);
lean_dec(x_9);
x_12 = x_135;
goto block_130;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_146 = l_Lean_Meta_Simp_mkImpCongr___closed__4;
x_147 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_146);
x_12 = x_147;
goto block_130;
}
block_130:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_mkImpCongr(x_21, x_24, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_13, 0, x_28);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
lean_ctor_set(x_13, 0, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_13);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_13);
lean_dec(x_12);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_free_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_mkImpCongr(x_49, x_52, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_59 = 1;
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_12);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_59);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_51, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_68 = x_51;
} else {
 lean_dec_ref(x_51);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_72 = x_48;
} else {
 lean_dec_ref(x_48);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_11);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_11, 0);
lean_dec(x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_76 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_79 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_mkImpCongr(x_77, x_80, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
lean_ctor_set(x_11, 0, x_84);
x_85 = 1;
x_86 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_11);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_85);
lean_ctor_set(x_82, 0, x_86);
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
lean_ctor_set(x_11, 0, x_87);
x_89 = 1;
x_90 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_11);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_free_object(x_11);
lean_dec(x_12);
x_92 = !lean_is_exclusive(x_82);
if (x_92 == 0)
{
return x_82;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_82, 0);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_77);
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_79);
if (x_96 == 0)
{
return x_79;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_79, 0);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_79);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_76);
if (x_100 == 0)
{
return x_76;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_76, 0);
x_102 = lean_ctor_get(x_76, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_76);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_104 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_107 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_mkImpCongr(x_105, x_108, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_115 = 1;
x_116 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_116, 0, x_12);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_115);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_12);
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_120 = x_110;
} else {
 lean_dec_ref(x_110);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_105);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_ctor_get(x_107, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_107, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_124 = x_107;
} else {
 lean_dec_ref(x_107);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_ctor_get(x_104, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_104, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_128 = x_104;
} else {
 lean_dec_ref(x_104);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3;
x_3 = lean_unsigned_to_nat(6u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5;
x_6 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7;
x_10 = l_Lean_Expr_isAppOf(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_appArg_x21(x_1);
x_12 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7;
x_13 = l_Lean_Expr_isAppOf(x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_4 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_appArg_x21(x_4);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_2, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = l_outOfBounds___rarg(x_21);
x_23 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
x_24 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
x_26 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_22);
x_27 = lean_array_set(x_17, x_2, x_26);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_27);
x_30 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_array_fget(x_17, x_2);
x_33 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
x_34 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
x_36 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_32);
x_37 = lean_array_set(x_17, x_2, x_36);
x_38 = 1;
x_39 = lean_box(x_38);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_37);
x_40 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_5);
x_44 = lean_array_get_size(x_42);
x_45 = lean_nat_dec_lt(x_2, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_instInhabitedExpr;
x_47 = l_outOfBounds___rarg(x_46);
x_48 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_50;
x_5 = x_49;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
x_52 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_47);
x_53 = lean_array_set(x_42, x_2, x_52);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_57;
x_5 = x_56;
goto _start;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_array_fget(x_42, x_2);
x_60 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_42);
lean_ctor_set(x_61, 1, x_43);
x_62 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_62;
x_5 = x_61;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_43);
x_64 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_59);
x_65 = lean_array_set(x_42, x_2, x_64);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_69;
x_5 = x_68;
goto _start;
}
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_10);
return x_72;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_7);
x_9 = l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_14);
x_18 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(x_14, x_7, x_14, x_11, x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_18, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_30 = l_Lean_mkAppN(x_29, x_28);
lean_dec(x_28);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_34 = l_Lean_mkAppN(x_33, x_32);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_7, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_7, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; double x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_17, 3);
x_21 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_22 = 0;
x_23 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_22);
x_25 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_11);
x_27 = l_Lean_PersistentArray_push___rarg(x_20, x_15);
lean_ctor_set(x_17, 3, x_27);
x_28 = lean_st_ref_set(x_9, x_17, x_19);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_15, 1);
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
x_38 = lean_ctor_get(x_17, 2);
x_39 = lean_ctor_get(x_17, 3);
x_40 = lean_ctor_get(x_17, 4);
x_41 = lean_ctor_get(x_17, 5);
x_42 = lean_ctor_get(x_17, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_43 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_44 = 0;
x_45 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_13);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_48);
lean_ctor_set(x_15, 0, x_11);
x_49 = l_Lean_PersistentArray_push___rarg(x_39, x_15);
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_38);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set(x_50, 4, x_40);
lean_ctor_set(x_50, 5, x_41);
lean_ctor_set(x_50, 6, x_42);
x_51 = lean_st_ref_set(x_9, x_50, x_35);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 6);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_67 = 0;
x_68 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_13);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_11);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_11);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_PersistentArray_push___rarg(x_61, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 7, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_59);
lean_ctor_set(x_74, 2, x_60);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_62);
lean_ctor_set(x_74, 5, x_63);
lean_ctor_set(x_74, 6, x_64);
x_75 = lean_st_ref_set(x_9, x_74, x_57);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_66; uint8_t x_67; 
x_66 = lean_array_fget(x_4, x_3);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 14);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 1);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = lean_simp(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_72 = l_Lean_Meta_Simp_mkCongr(x_6, x_70, x_11, x_12, x_13, x_14, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_box(0);
x_76 = lean_apply_11(x_2, x_3, x_73, x_75, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
return x_69;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_69, 0);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_69);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; 
x_85 = lean_box(0);
x_16 = x_85;
goto block_65;
}
}
else
{
uint8_t x_86; 
x_86 = l_Lean_Meta_ParamInfo_isInstImplicit(x_66);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 1);
lean_dec(x_66);
if (x_87 == 0)
{
lean_object* x_88; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_88 = lean_simp(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_91 = l_Lean_Meta_Simp_mkCongr(x_6, x_89, x_11, x_12, x_13, x_14, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = lean_apply_11(x_2, x_3, x_92, x_94, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; 
x_104 = lean_box(0);
x_16 = x_104;
goto block_65;
}
}
else
{
lean_object* x_105; 
lean_dec(x_66);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_105 = l_Lean_Meta_Simp_mkCongrFun(x_6, x_1, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
x_109 = lean_apply_11(x_2, x_3, x_106, x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_107);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
block_65:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_18 = lean_infer_type(x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_21 = l_Lean_Meta_whnfD(x_19, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isArrow(x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = lean_dsimp(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_28 = l_Lean_Meta_Simp_mkCongrFun(x_6, x_26, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = lean_apply_11(x_2, x_3, x_29, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_41 = lean_simp(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_44 = l_Lean_Meta_Simp_mkCongr(x_6, x_42, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_apply_11(x_2, x_3, x_45, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
return x_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
return x_21;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app [", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_17 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_dec(x_6);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1;
x_30 = lean_array_get_size(x_2);
x_31 = lean_nat_dec_lt(x_27, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = lean_infer_type(x_32, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_36 = l_Lean_Meta_whnfD(x_34, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_isArrow(x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = lean_dsimp(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_43 = l_Lean_Meta_Simp_mkCongrFun(x_28, x_41, x_10, x_11, x_12, x_13, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_47 = lean_apply_11(x_29, x_27, x_44, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_18 = x_48;
x_19 = x_49;
goto block_26;
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_40);
if (x_58 == 0)
{
return x_40;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = lean_simp(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_65 = l_Lean_Meta_Simp_mkCongr(x_28, x_63, x_10, x_11, x_12, x_13, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_69 = lean_apply_11(x_29, x_27, x_66, x_68, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_18 = x_70;
x_19 = x_71;
goto block_26;
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_65);
if (x_76 == 0)
{
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 0);
x_78 = lean_ctor_get(x_65, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_65);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_62);
if (x_80 == 0)
{
return x_62;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_62, 0);
x_82 = lean_ctor_get(x_62, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_62);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_84 = !lean_is_exclusive(x_36);
if (x_84 == 0)
{
return x_36;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_36, 0);
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_36);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_33);
if (x_88 == 0)
{
return x_33;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_33, 0);
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_33);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6;
x_93 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_92, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_30);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_98 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_97, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_18 = x_99;
x_19 = x_100;
goto block_26;
}
else
{
uint8_t x_101; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_93);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_106 = lean_ctor_get(x_93, 1);
x_107 = lean_ctor_get(x_93, 0);
lean_dec(x_107);
lean_inc(x_27);
x_108 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_Lean_MessageData_ofFormat(x_109);
x_111 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_110);
lean_ctor_set(x_93, 0, x_111);
x_112 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_93);
lean_ctor_set(x_113, 1, x_112);
x_114 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_MessageData_ofFormat(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_17);
x_120 = l_Lean_MessageData_ofExpr(x_17);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_fget(x_2, x_27);
x_125 = lean_ctor_get_uint8(x_124, sizeof(void*)*1 + 1);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_129, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_106);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_133 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_131, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_132);
lean_dec(x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_18 = x_134;
x_19 = x_135;
goto block_26;
}
else
{
uint8_t x_136; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_123);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_143, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_106);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_147 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_145, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_146);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_18 = x_148;
x_19 = x_149;
goto block_26;
}
else
{
uint8_t x_150; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_147);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_154 = lean_ctor_get(x_93, 1);
lean_inc(x_154);
lean_dec(x_93);
lean_inc(x_27);
x_155 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_MessageData_ofFormat(x_156);
x_158 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_163 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_MessageData_ofFormat(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_17);
x_168 = l_Lean_MessageData_ofExpr(x_17);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_fget(x_2, x_27);
x_173 = lean_ctor_get_uint8(x_172, sizeof(void*)*1 + 1);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_154);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_181 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_179, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_180);
lean_dec(x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_18 = x_182;
x_19 = x_183;
goto block_26;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_188 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_171);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_191, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_154);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_195 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_193, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_194);
lean_dec(x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_18 = x_196;
x_19 = x_197;
goto block_26;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Simp_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_getFunInfoNArgs(x_16, x_17, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_array_size(x_2);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_14, x_21, x_2, x_23, x_24, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
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
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_getFunInfoNArgs(x_43, x_44, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_1);
x_51 = lean_array_size(x_2);
x_52 = 0;
x_53 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_41, x_48, x_2, x_51, x_52, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_48);
lean_dec(x_41);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_45, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_65 = x_45;
} else {
 lean_dec_ref(x_45);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_10);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_congrArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = lean_box(x_6);
switch (lean_obj_tag(x_7)) {
case 0:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
case 2:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
goto _start;
}
default: 
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = 1;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_is_matcher(x_13, x_1);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_is_matcher(x_18, x_1);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Expr_hash(x_1);
x_22 = 32;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = 16;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = 1;
x_31 = lean_usize_sub(x_29, x_30);
x_32 = lean_usize_land(x_28, x_31);
x_33 = lean_array_uget(x_19, x_32);
lean_dec(x_19);
x_34 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(x_1, x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_free_object(x_13);
x_35 = 1;
lean_inc(x_1);
x_36 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_2, x_3, x_35, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_7, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
x_48 = lean_array_get_size(x_47);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = lean_usize_sub(x_49, x_30);
x_51 = lean_usize_land(x_28, x_50);
x_52 = lean_array_uget(x_47, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_46, x_54);
lean_dec(x_46);
lean_inc(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_47, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_57);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_55);
x_65 = lean_st_ref_set(x_7, x_40, x_42);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_37);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_37);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_ctor_set(x_41, 1, x_57);
lean_ctor_set(x_41, 0, x_55);
x_70 = lean_st_ref_set(x_7, x_40, x_42);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_37);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_37);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_47, x_51, x_75);
lean_inc(x_37);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_37, x_52);
x_78 = lean_array_uset(x_76, x_51, x_77);
lean_ctor_set(x_41, 1, x_78);
x_79 = lean_st_ref_set(x_7, x_40, x_42);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_37);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_37);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; uint8_t x_91; 
x_84 = lean_ctor_get(x_41, 0);
x_85 = lean_ctor_get(x_41, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_41);
x_86 = lean_array_get_size(x_85);
x_87 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_88 = lean_usize_sub(x_87, x_30);
x_89 = lean_usize_land(x_28, x_88);
x_90 = lean_array_uget(x_85, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_84, x_92);
lean_dec(x_84);
lean_inc(x_37);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_37);
lean_ctor_set(x_94, 2, x_90);
x_95 = lean_array_uset(x_85, x_89, x_94);
x_96 = lean_unsigned_to_nat(4u);
x_97 = lean_nat_mul(x_93, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_nat_div(x_97, x_98);
lean_dec(x_97);
x_100 = lean_array_get_size(x_95);
x_101 = lean_nat_dec_le(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_95);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_40, 1, x_103);
x_104 = lean_st_ref_set(x_7, x_40, x_42);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_95);
lean_ctor_set(x_40, 1, x_108);
x_109 = lean_st_ref_set(x_7, x_40, x_42);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_37);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_box(0);
x_114 = lean_array_uset(x_85, x_89, x_113);
lean_inc(x_37);
x_115 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_37, x_90);
x_116 = lean_array_uset(x_114, x_89, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_84);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_40, 1, x_117);
x_118 = lean_st_ref_set(x_7, x_40, x_42);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_37);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; size_t x_131; size_t x_132; lean_object* x_133; uint8_t x_134; 
x_122 = lean_ctor_get(x_40, 0);
x_123 = lean_ctor_get(x_40, 2);
x_124 = lean_ctor_get(x_40, 3);
x_125 = lean_ctor_get(x_40, 4);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_40);
x_126 = lean_ctor_get(x_41, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_41, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_128 = x_41;
} else {
 lean_dec_ref(x_41);
 x_128 = lean_box(0);
}
x_129 = lean_array_get_size(x_127);
x_130 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_131 = lean_usize_sub(x_130, x_30);
x_132 = lean_usize_land(x_28, x_131);
x_133 = lean_array_uget(x_127, x_132);
x_134 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_126, x_135);
lean_dec(x_126);
lean_inc(x_37);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_37);
lean_ctor_set(x_137, 2, x_133);
x_138 = lean_array_uset(x_127, x_132, x_137);
x_139 = lean_unsigned_to_nat(4u);
x_140 = lean_nat_mul(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_138);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_122);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_123);
lean_ctor_set(x_147, 3, x_124);
lean_ctor_set(x_147, 4, x_125);
x_148 = lean_st_ref_set(x_7, x_147, x_42);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_37);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
if (lean_is_scalar(x_128)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_128;
}
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_138);
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_122);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_123);
lean_ctor_set(x_153, 3, x_124);
lean_ctor_set(x_153, 4, x_125);
x_154 = lean_st_ref_set(x_7, x_153, x_42);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_37);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_box(0);
x_159 = lean_array_uset(x_127, x_132, x_158);
lean_inc(x_37);
x_160 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_37, x_133);
x_161 = lean_array_uset(x_159, x_132, x_160);
if (lean_is_scalar(x_128)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_128;
}
lean_ctor_set(x_162, 0, x_126);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_163, 0, x_122);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_123);
lean_ctor_set(x_163, 3, x_124);
lean_ctor_set(x_163, 4, x_125);
x_164 = lean_st_ref_set(x_7, x_163, x_42);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_37);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_36);
if (x_168 == 0)
{
return x_36;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_36, 0);
x_170 = lean_ctor_get(x_36, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_36);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_34, 0);
lean_inc(x_172);
lean_dec(x_34);
lean_ctor_set(x_13, 0, x_172);
return x_13;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; size_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; lean_object* x_188; lean_object* x_189; 
x_173 = lean_ctor_get(x_13, 1);
lean_inc(x_173);
lean_dec(x_13);
x_174 = lean_ctor_get(x_15, 1);
lean_inc(x_174);
lean_dec(x_15);
x_175 = lean_array_get_size(x_174);
x_176 = l_Lean_Expr_hash(x_1);
x_177 = 32;
x_178 = lean_uint64_shift_right(x_176, x_177);
x_179 = lean_uint64_xor(x_176, x_178);
x_180 = 16;
x_181 = lean_uint64_shift_right(x_179, x_180);
x_182 = lean_uint64_xor(x_179, x_181);
x_183 = lean_uint64_to_usize(x_182);
x_184 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_185 = 1;
x_186 = lean_usize_sub(x_184, x_185);
x_187 = lean_usize_land(x_183, x_186);
x_188 = lean_array_uget(x_174, x_187);
lean_dec(x_174);
x_189 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(x_1, x_188);
lean_dec(x_188);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; lean_object* x_191; 
x_190 = 1;
lean_inc(x_1);
x_191 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_2, x_3, x_190, x_8, x_9, x_10, x_11, x_173);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; size_t x_207; size_t x_208; size_t x_209; lean_object* x_210; uint8_t x_211; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_take(x_7, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 4);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_196, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_205 = x_196;
} else {
 lean_dec_ref(x_196);
 x_205 = lean_box(0);
}
x_206 = lean_array_get_size(x_204);
x_207 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_208 = lean_usize_sub(x_207, x_185);
x_209 = lean_usize_land(x_183, x_208);
x_210 = lean_array_uget(x_204, x_209);
x_211 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_nat_add(x_203, x_212);
lean_dec(x_203);
lean_inc(x_192);
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_1);
lean_ctor_set(x_214, 1, x_192);
lean_ctor_set(x_214, 2, x_210);
x_215 = lean_array_uset(x_204, x_209, x_214);
x_216 = lean_unsigned_to_nat(4u);
x_217 = lean_nat_mul(x_213, x_216);
x_218 = lean_unsigned_to_nat(3u);
x_219 = lean_nat_div(x_217, x_218);
lean_dec(x_217);
x_220 = lean_array_get_size(x_215);
x_221 = lean_nat_dec_le(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_215);
if (lean_is_scalar(x_205)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_205;
}
lean_ctor_set(x_223, 0, x_213);
lean_ctor_set(x_223, 1, x_222);
if (lean_is_scalar(x_202)) {
 x_224 = lean_alloc_ctor(0, 5, 0);
} else {
 x_224 = x_202;
}
lean_ctor_set(x_224, 0, x_198);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_199);
lean_ctor_set(x_224, 3, x_200);
lean_ctor_set(x_224, 4, x_201);
x_225 = lean_st_ref_set(x_7, x_224, x_197);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_192);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
if (lean_is_scalar(x_205)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_205;
}
lean_ctor_set(x_229, 0, x_213);
lean_ctor_set(x_229, 1, x_215);
if (lean_is_scalar(x_202)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_202;
}
lean_ctor_set(x_230, 0, x_198);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_199);
lean_ctor_set(x_230, 3, x_200);
lean_ctor_set(x_230, 4, x_201);
x_231 = lean_st_ref_set(x_7, x_230, x_197);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_192);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_235 = lean_box(0);
x_236 = lean_array_uset(x_204, x_209, x_235);
lean_inc(x_192);
x_237 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_1, x_192, x_210);
x_238 = lean_array_uset(x_236, x_209, x_237);
if (lean_is_scalar(x_205)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_205;
}
lean_ctor_set(x_239, 0, x_203);
lean_ctor_set(x_239, 1, x_238);
if (lean_is_scalar(x_202)) {
 x_240 = lean_alloc_ctor(0, 5, 0);
} else {
 x_240 = x_202;
}
lean_ctor_set(x_240, 0, x_198);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_199);
lean_ctor_set(x_240, 3, x_200);
lean_ctor_set(x_240, 4, x_201);
x_241 = lean_st_ref_set(x_7, x_240, x_197);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_192);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_1);
x_245 = lean_ctor_get(x_191, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_191, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_247 = x_191;
} else {
 lean_dec_ref(x_191);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_189, 0);
lean_inc(x_249);
lean_dec(x_189);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_173);
return x_250;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_getFunInfo(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_Meta_getCongrSimpKinds(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_array_get_size(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(x_16, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_14);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(x_1, x_12, x_16, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_array_get_size(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
size_t x_35; size_t x_36; uint8_t x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_37 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(x_28, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
x_41 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(x_1, x_12, x_28, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isConst(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Expr_constName_x21(x_1);
x_14 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
x_19 = lean_box(x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_array_push(x_7, x_1);
x_19 = lean_box(0);
x_20 = lean_box(x_4);
x_21 = lean_box(x_5);
x_22 = lean_box(x_8);
x_23 = lean_apply_15(x_2, x_3, x_18, x_20, x_21, x_6, x_22, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_expr_eqv(x_1, x_2);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = 1;
x_21 = lean_box(0);
x_22 = lean_box(x_6);
x_23 = lean_box(x_8);
x_24 = lean_box(x_20);
x_25 = lean_apply_15(x_3, x_4, x_5, x_22, x_23, x_7, x_24, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_box(0);
x_27 = lean_box(x_6);
x_28 = lean_box(x_8);
x_29 = lean_box(x_9);
x_30 = lean_apply_15(x_3, x_4, x_5, x_27, x_28, x_7, x_29, x_26, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_30;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(561u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed), 16, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = lean_box(x_2);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; 
lean_dec(x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_21 = lean_dsimp(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_expr_eqv(x_3, x_22);
lean_dec(x_3);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_box(0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_22, x_19, x_4, x_6, x_7, x_8, x_5, x_25, x_26, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_22, x_19, x_4, x_6, x_7, x_8, x_5, x_9, x_28, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 2:
{
lean_object* x_34; 
lean_dec(x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_34 = lean_simp(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_35);
x_37 = lean_array_push(x_4, x_35);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_inc(x_38);
x_39 = lean_array_push(x_5, x_38);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_3, x_38, x_19, x_37, x_39, x_6, x_8, x_7, x_9, x_41, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_36);
lean_dec(x_38);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_43 = 1;
x_44 = lean_box(0);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_3, x_38, x_19, x_37, x_39, x_6, x_8, x_43, x_9, x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_36);
lean_dec(x_38);
lean_dec(x_3);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 3:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_19);
x_50 = lean_array_push(x_5, x_3);
x_51 = 1;
x_52 = lean_box(0);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_50, x_51, x_7, x_8, x_9, x_52, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
return x_53;
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_19);
x_54 = lean_array_push(x_5, x_3);
x_55 = lean_box(0);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_54, x_6, x_7, x_8, x_9, x_55, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_58 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(x_57, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_59, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_60);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_59);
lean_dec(x_8);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_array_uget(x_4, x_6);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_7);
lean_ctor_set(x_46, 1, x_15);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_25, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_25, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_25, 0);
lean_dec(x_50);
x_51 = lean_array_fget(x_42, x_43);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_43, x_53);
lean_dec(x_43);
lean_ctor_set(x_25, 1, x_54);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_56 = lean_box(0);
x_57 = lean_unbox(x_34);
lean_dec(x_34);
x_58 = lean_unbox(x_37);
lean_dec(x_37);
x_59 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_25, x_52, x_18, x_28, x_31, x_57, x_58, x_40, x_59, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; 
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_dec(x_60);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
lean_dec(x_61);
x_70 = 1;
x_71 = lean_usize_add(x_6, x_70);
x_6 = x_71;
x_7 = x_69;
x_15 = x_68;
goto _start;
}
}
else
{
uint8_t x_73; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_array_get_size(x_2);
x_78 = lean_nat_dec_lt(x_40, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_79 = lean_box(0);
x_80 = lean_unbox(x_34);
lean_dec(x_34);
x_81 = lean_unbox(x_37);
lean_dec(x_37);
x_82 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_83 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_25, x_52, x_18, x_28, x_31, x_80, x_81, x_40, x_82, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; 
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
lean_dec(x_84);
x_93 = 1;
x_94 = lean_usize_add(x_6, x_93);
x_6 = x_94;
x_7 = x_92;
x_15 = x_91;
goto _start;
}
}
else
{
uint8_t x_96; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_96 = !lean_is_exclusive(x_83);
if (x_96 == 0)
{
return x_83;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_83, 0);
x_98 = lean_ctor_get(x_83, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_83);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_array_fget(x_2, x_40);
x_101 = l_Lean_Meta_ParamInfo_isInstImplicit(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_102 = lean_box(0);
x_103 = lean_unbox(x_34);
lean_dec(x_34);
x_104 = lean_unbox(x_37);
lean_dec(x_37);
x_105 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_106 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_25, x_52, x_18, x_28, x_31, x_103, x_104, x_40, x_105, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; 
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_dec(x_106);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
lean_dec(x_107);
x_116 = 1;
x_117 = lean_usize_add(x_6, x_116);
x_6 = x_117;
x_7 = x_115;
x_15 = x_114;
goto _start;
}
}
else
{
uint8_t x_119; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
return x_106;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_106, 0);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_106);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; size_t x_125; size_t x_126; 
x_123 = lean_array_push(x_31, x_18);
x_124 = lean_nat_add(x_40, x_53);
lean_dec(x_40);
lean_ctor_set(x_23, 0, x_124);
lean_ctor_set(x_20, 0, x_123);
x_125 = 1;
x_126 = lean_usize_add(x_6, x_125);
x_6 = x_126;
goto _start;
}
}
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_25);
x_128 = lean_array_fget(x_42, x_43);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_43, x_130);
lean_dec(x_43);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_44);
x_133 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_134 = lean_box(0);
x_135 = lean_unbox(x_34);
lean_dec(x_34);
x_136 = lean_unbox(x_37);
lean_dec(x_37);
x_137 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_138 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_132, x_129, x_18, x_28, x_31, x_135, x_136, x_40, x_137, x_134, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
lean_dec(x_139);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; size_t x_146; size_t x_147; 
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_146 = 1;
x_147 = lean_usize_add(x_6, x_146);
x_6 = x_147;
x_7 = x_145;
x_15 = x_144;
goto _start;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_149 = lean_ctor_get(x_138, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_138, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_151 = x_138;
} else {
 lean_dec_ref(x_138);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_array_get_size(x_2);
x_154 = lean_nat_dec_lt(x_40, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_155 = lean_box(0);
x_156 = lean_unbox(x_34);
lean_dec(x_34);
x_157 = lean_unbox(x_37);
lean_dec(x_37);
x_158 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_159 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_132, x_129, x_18, x_28, x_31, x_156, x_157, x_40, x_158, x_155, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
lean_dec(x_160);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; 
x_165 = lean_ctor_get(x_159, 1);
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
lean_dec(x_160);
x_167 = 1;
x_168 = lean_usize_add(x_6, x_167);
x_6 = x_168;
x_7 = x_166;
x_15 = x_165;
goto _start;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_170 = lean_ctor_get(x_159, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_159, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_172 = x_159;
} else {
 lean_dec_ref(x_159);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_array_fget(x_2, x_40);
x_175 = l_Lean_Meta_ParamInfo_isInstImplicit(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_176 = lean_box(0);
x_177 = lean_unbox(x_34);
lean_dec(x_34);
x_178 = lean_unbox(x_37);
lean_dec(x_37);
x_179 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_180 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_132, x_129, x_18, x_28, x_31, x_177, x_178, x_40, x_179, x_176, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
lean_dec(x_181);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; size_t x_188; size_t x_189; 
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_dec(x_180);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
lean_dec(x_181);
x_188 = 1;
x_189 = lean_usize_add(x_6, x_188);
x_6 = x_189;
x_7 = x_187;
x_15 = x_186;
goto _start;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_191 = lean_ctor_get(x_180, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_193 = x_180;
} else {
 lean_dec_ref(x_180);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; size_t x_197; size_t x_198; 
x_195 = lean_array_push(x_31, x_18);
x_196 = lean_nat_add(x_40, x_130);
lean_dec(x_40);
lean_ctor_set(x_23, 0, x_196);
lean_ctor_set(x_20, 0, x_195);
lean_ctor_set(x_7, 0, x_132);
x_197 = 1;
x_198 = lean_usize_add(x_6, x_197);
x_6 = x_198;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_23, 0);
x_201 = lean_ctor_get(x_23, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_23);
x_202 = lean_ctor_get(x_25, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_25, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_25, 2);
lean_inc(x_204);
x_205 = lean_nat_dec_lt(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_201);
lean_ctor_set(x_22, 1, x_206);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_7);
lean_ctor_set(x_207, 1, x_15);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_208 = x_25;
} else {
 lean_dec_ref(x_25);
 x_208 = lean_box(0);
}
x_209 = lean_array_fget(x_202, x_203);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_203, x_211);
lean_dec(x_203);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(0, 3, 0);
} else {
 x_213 = x_208;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_213, 2, x_204);
x_214 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; lean_object* x_219; 
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_215 = lean_box(0);
x_216 = lean_unbox(x_34);
lean_dec(x_34);
x_217 = lean_unbox(x_37);
lean_dec(x_37);
x_218 = lean_unbox(x_201);
lean_dec(x_201);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_219 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_213, x_210, x_18, x_28, x_31, x_216, x_217, x_200, x_218, x_215, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
lean_dec(x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; size_t x_227; size_t x_228; 
x_225 = lean_ctor_get(x_219, 1);
lean_inc(x_225);
lean_dec(x_219);
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
lean_dec(x_220);
x_227 = 1;
x_228 = lean_usize_add(x_6, x_227);
x_6 = x_228;
x_7 = x_226;
x_15 = x_225;
goto _start;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_230 = lean_ctor_get(x_219, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_219, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_232 = x_219;
} else {
 lean_dec_ref(x_219);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_array_get_size(x_2);
x_235 = lean_nat_dec_lt(x_200, x_234);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; lean_object* x_240; 
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_236 = lean_box(0);
x_237 = lean_unbox(x_34);
lean_dec(x_34);
x_238 = lean_unbox(x_37);
lean_dec(x_37);
x_239 = lean_unbox(x_201);
lean_dec(x_201);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_240 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_213, x_210, x_18, x_28, x_31, x_237, x_238, x_200, x_239, x_236, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
lean_dec(x_241);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; 
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
lean_dec(x_240);
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
lean_dec(x_241);
x_248 = 1;
x_249 = lean_usize_add(x_6, x_248);
x_6 = x_249;
x_7 = x_247;
x_15 = x_246;
goto _start;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_251 = lean_ctor_get(x_240, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_240, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_253 = x_240;
} else {
 lean_dec_ref(x_240);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_array_fget(x_2, x_200);
x_256 = l_Lean_Meta_ParamInfo_isInstImplicit(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; lean_object* x_261; 
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_257 = lean_box(0);
x_258 = lean_unbox(x_34);
lean_dec(x_34);
x_259 = lean_unbox(x_37);
lean_dec(x_37);
x_260 = lean_unbox(x_201);
lean_dec(x_201);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_261 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_213, x_210, x_18, x_28, x_31, x_258, x_259, x_200, x_260, x_257, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; size_t x_269; size_t x_270; 
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_dec(x_261);
x_268 = lean_ctor_get(x_262, 0);
lean_inc(x_268);
lean_dec(x_262);
x_269 = 1;
x_270 = lean_usize_add(x_6, x_269);
x_6 = x_270;
x_7 = x_268;
x_15 = x_267;
goto _start;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_272 = lean_ctor_get(x_261, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_261, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_274 = x_261;
} else {
 lean_dec_ref(x_261);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; size_t x_279; size_t x_280; 
x_276 = lean_array_push(x_31, x_18);
x_277 = lean_nat_add(x_200, x_211);
lean_dec(x_200);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_201);
lean_ctor_set(x_22, 1, x_278);
lean_ctor_set(x_20, 0, x_276);
lean_ctor_set(x_7, 0, x_213);
x_279 = 1;
x_280 = lean_usize_add(x_6, x_279);
x_6 = x_280;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_282 = lean_ctor_get(x_22, 0);
lean_inc(x_282);
lean_dec(x_22);
x_283 = lean_ctor_get(x_23, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_23, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_285 = x_23;
} else {
 lean_dec_ref(x_23);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_25, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_25, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_25, 2);
lean_inc(x_288);
x_289 = lean_nat_dec_lt(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_283);
lean_ctor_set(x_290, 1, x_284);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_282);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_21, 1, x_291);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_7);
lean_ctor_set(x_292, 1, x_15);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_293 = x_25;
} else {
 lean_dec_ref(x_25);
 x_293 = lean_box(0);
}
x_294 = lean_array_fget(x_286, x_287);
x_295 = lean_unbox(x_294);
lean_dec(x_294);
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_nat_add(x_287, x_296);
lean_dec(x_287);
if (lean_is_scalar(x_293)) {
 x_298 = lean_alloc_ctor(0, 3, 0);
} else {
 x_298 = x_293;
}
lean_ctor_set(x_298, 0, x_286);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_288);
x_299 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_299 == 0)
{
lean_object* x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; lean_object* x_304; 
lean_dec(x_285);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_300 = lean_box(0);
x_301 = lean_unbox(x_34);
lean_dec(x_34);
x_302 = lean_unbox(x_282);
lean_dec(x_282);
x_303 = lean_unbox(x_284);
lean_dec(x_284);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_304 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_298, x_295, x_18, x_28, x_31, x_301, x_302, x_283, x_303, x_300, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_307 = x_304;
} else {
 lean_dec_ref(x_304);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
lean_dec(x_305);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; size_t x_312; size_t x_313; 
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_dec(x_304);
x_311 = lean_ctor_get(x_305, 0);
lean_inc(x_311);
lean_dec(x_305);
x_312 = 1;
x_313 = lean_usize_add(x_6, x_312);
x_6 = x_313;
x_7 = x_311;
x_15 = x_310;
goto _start;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_315 = lean_ctor_get(x_304, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_304, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_317 = x_304;
} else {
 lean_dec_ref(x_304);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_array_get_size(x_2);
x_320 = lean_nat_dec_lt(x_283, x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; lean_object* x_325; 
lean_dec(x_285);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_321 = lean_box(0);
x_322 = lean_unbox(x_34);
lean_dec(x_34);
x_323 = lean_unbox(x_282);
lean_dec(x_282);
x_324 = lean_unbox(x_284);
lean_dec(x_284);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_325 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_298, x_295, x_18, x_28, x_31, x_322, x_323, x_283, x_324, x_321, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_326, 0);
lean_inc(x_329);
lean_dec(x_326);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; size_t x_333; size_t x_334; 
x_331 = lean_ctor_get(x_325, 1);
lean_inc(x_331);
lean_dec(x_325);
x_332 = lean_ctor_get(x_326, 0);
lean_inc(x_332);
lean_dec(x_326);
x_333 = 1;
x_334 = lean_usize_add(x_6, x_333);
x_6 = x_334;
x_7 = x_332;
x_15 = x_331;
goto _start;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_336 = lean_ctor_get(x_325, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_325, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_338 = x_325;
} else {
 lean_dec_ref(x_325);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_array_fget(x_2, x_283);
x_341 = l_Lean_Meta_ParamInfo_isInstImplicit(x_340);
lean_dec(x_340);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; 
lean_dec(x_285);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_342 = lean_box(0);
x_343 = lean_unbox(x_34);
lean_dec(x_34);
x_344 = lean_unbox(x_282);
lean_dec(x_282);
x_345 = lean_unbox(x_284);
lean_dec(x_284);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_346 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_298, x_295, x_18, x_28, x_31, x_343, x_344, x_283, x_345, x_342, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_347, 0);
lean_inc(x_350);
lean_dec(x_347);
if (lean_is_scalar(x_349)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_349;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_348);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; size_t x_354; size_t x_355; 
x_352 = lean_ctor_get(x_346, 1);
lean_inc(x_352);
lean_dec(x_346);
x_353 = lean_ctor_get(x_347, 0);
lean_inc(x_353);
lean_dec(x_347);
x_354 = 1;
x_355 = lean_usize_add(x_6, x_354);
x_6 = x_355;
x_7 = x_353;
x_15 = x_352;
goto _start;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_357 = lean_ctor_get(x_346, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_346, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; size_t x_365; size_t x_366; 
x_361 = lean_array_push(x_31, x_18);
x_362 = lean_nat_add(x_283, x_296);
lean_dec(x_283);
if (lean_is_scalar(x_285)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_285;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_284);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_282);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set(x_21, 1, x_364);
lean_ctor_set(x_20, 0, x_361);
lean_ctor_set(x_7, 0, x_298);
x_365 = 1;
x_366 = lean_usize_add(x_6, x_365);
x_6 = x_366;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_368 = lean_ctor_get(x_21, 0);
lean_inc(x_368);
lean_dec(x_21);
x_369 = lean_ctor_get(x_22, 0);
lean_inc(x_369);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_370 = x_22;
} else {
 lean_dec_ref(x_22);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_23, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_23, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_373 = x_23;
} else {
 lean_dec_ref(x_23);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_25, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_25, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_25, 2);
lean_inc(x_376);
x_377 = lean_nat_dec_lt(x_375, x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_373)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_373;
}
lean_ctor_set(x_378, 0, x_371);
lean_ctor_set(x_378, 1, x_372);
if (lean_is_scalar(x_370)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_370;
}
lean_ctor_set(x_379, 0, x_369);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_20, 1, x_380);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_7);
lean_ctor_set(x_381, 1, x_15);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_382 = x_25;
} else {
 lean_dec_ref(x_25);
 x_382 = lean_box(0);
}
x_383 = lean_array_fget(x_374, x_375);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
x_385 = lean_unsigned_to_nat(1u);
x_386 = lean_nat_add(x_375, x_385);
lean_dec(x_375);
if (lean_is_scalar(x_382)) {
 x_387 = lean_alloc_ctor(0, 3, 0);
} else {
 x_387 = x_382;
}
lean_ctor_set(x_387, 0, x_374);
lean_ctor_set(x_387, 1, x_386);
lean_ctor_set(x_387, 2, x_376);
x_388 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; lean_object* x_393; 
lean_dec(x_373);
lean_dec(x_370);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_389 = lean_box(0);
x_390 = lean_unbox(x_368);
lean_dec(x_368);
x_391 = lean_unbox(x_369);
lean_dec(x_369);
x_392 = lean_unbox(x_372);
lean_dec(x_372);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_393 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_387, x_384, x_18, x_28, x_31, x_390, x_391, x_371, x_392, x_389, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_396 = x_393;
} else {
 lean_dec_ref(x_393);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
lean_dec(x_394);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_395);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; size_t x_401; size_t x_402; 
x_399 = lean_ctor_get(x_393, 1);
lean_inc(x_399);
lean_dec(x_393);
x_400 = lean_ctor_get(x_394, 0);
lean_inc(x_400);
lean_dec(x_394);
x_401 = 1;
x_402 = lean_usize_add(x_6, x_401);
x_6 = x_402;
x_7 = x_400;
x_15 = x_399;
goto _start;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_404 = lean_ctor_get(x_393, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_393, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_406 = x_393;
} else {
 lean_dec_ref(x_393);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
else
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_array_get_size(x_2);
x_409 = lean_nat_dec_lt(x_371, x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; uint8_t x_411; uint8_t x_412; uint8_t x_413; lean_object* x_414; 
lean_dec(x_373);
lean_dec(x_370);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_410 = lean_box(0);
x_411 = lean_unbox(x_368);
lean_dec(x_368);
x_412 = lean_unbox(x_369);
lean_dec(x_369);
x_413 = lean_unbox(x_372);
lean_dec(x_372);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_414 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_387, x_384, x_18, x_28, x_31, x_411, x_412, x_371, x_413, x_410, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_417 = x_414;
} else {
 lean_dec_ref(x_414);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
lean_dec(x_415);
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_416);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; size_t x_422; size_t x_423; 
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
lean_dec(x_414);
x_421 = lean_ctor_get(x_415, 0);
lean_inc(x_421);
lean_dec(x_415);
x_422 = 1;
x_423 = lean_usize_add(x_6, x_422);
x_6 = x_423;
x_7 = x_421;
x_15 = x_420;
goto _start;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_425 = lean_ctor_get(x_414, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_414, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_427 = x_414;
} else {
 lean_dec_ref(x_414);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
else
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_array_fget(x_2, x_371);
x_430 = l_Lean_Meta_ParamInfo_isInstImplicit(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; lean_object* x_435; 
lean_dec(x_373);
lean_dec(x_370);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_7);
x_431 = lean_box(0);
x_432 = lean_unbox(x_368);
lean_dec(x_368);
x_433 = lean_unbox(x_369);
lean_dec(x_369);
x_434 = lean_unbox(x_372);
lean_dec(x_372);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_435 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_387, x_384, x_18, x_28, x_31, x_432, x_433, x_371, x_434, x_431, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_436, 0);
lean_inc(x_439);
lean_dec(x_436);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_437);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; size_t x_443; size_t x_444; 
x_441 = lean_ctor_get(x_435, 1);
lean_inc(x_441);
lean_dec(x_435);
x_442 = lean_ctor_get(x_436, 0);
lean_inc(x_442);
lean_dec(x_436);
x_443 = 1;
x_444 = lean_usize_add(x_6, x_443);
x_6 = x_444;
x_7 = x_442;
x_15 = x_441;
goto _start;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_446 = lean_ctor_get(x_435, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_435, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_448 = x_435;
} else {
 lean_dec_ref(x_435);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; size_t x_455; size_t x_456; 
x_450 = lean_array_push(x_31, x_18);
x_451 = lean_nat_add(x_371, x_385);
lean_dec(x_371);
if (lean_is_scalar(x_373)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_373;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_372);
if (lean_is_scalar(x_370)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_370;
}
lean_ctor_set(x_453, 0, x_369);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_368);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set(x_20, 1, x_454);
lean_ctor_set(x_20, 0, x_450);
lean_ctor_set(x_7, 0, x_387);
x_455 = 1;
x_456 = lean_usize_add(x_6, x_455);
x_6 = x_456;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_458 = lean_ctor_get(x_20, 0);
lean_inc(x_458);
lean_dec(x_20);
x_459 = lean_ctor_get(x_21, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_460 = x_21;
} else {
 lean_dec_ref(x_21);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_22, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_462 = x_22;
} else {
 lean_dec_ref(x_22);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_23, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_23, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_465 = x_23;
} else {
 lean_dec_ref(x_23);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_25, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_25, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_25, 2);
lean_inc(x_468);
x_469 = lean_nat_dec_lt(x_467, x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_465)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_465;
}
lean_ctor_set(x_470, 0, x_463);
lean_ctor_set(x_470, 1, x_464);
if (lean_is_scalar(x_462)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_462;
}
lean_ctor_set(x_471, 0, x_461);
lean_ctor_set(x_471, 1, x_470);
if (lean_is_scalar(x_460)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_460;
}
lean_ctor_set(x_472, 0, x_459);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_458);
lean_ctor_set(x_473, 1, x_472);
lean_ctor_set(x_19, 1, x_473);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_7);
lean_ctor_set(x_474, 1, x_15);
return x_474;
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_475 = x_25;
} else {
 lean_dec_ref(x_25);
 x_475 = lean_box(0);
}
x_476 = lean_array_fget(x_466, x_467);
x_477 = lean_unbox(x_476);
lean_dec(x_476);
x_478 = lean_unsigned_to_nat(1u);
x_479 = lean_nat_add(x_467, x_478);
lean_dec(x_467);
if (lean_is_scalar(x_475)) {
 x_480 = lean_alloc_ctor(0, 3, 0);
} else {
 x_480 = x_475;
}
lean_ctor_set(x_480, 0, x_466);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_480, 2, x_468);
x_481 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_481 == 0)
{
lean_object* x_482; uint8_t x_483; uint8_t x_484; uint8_t x_485; lean_object* x_486; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_460);
lean_free_object(x_19);
lean_free_object(x_7);
x_482 = lean_box(0);
x_483 = lean_unbox(x_459);
lean_dec(x_459);
x_484 = lean_unbox(x_461);
lean_dec(x_461);
x_485 = lean_unbox(x_464);
lean_dec(x_464);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_486 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_480, x_477, x_18, x_28, x_458, x_483, x_484, x_463, x_485, x_482, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_489 = x_486;
} else {
 lean_dec_ref(x_486);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_487, 0);
lean_inc(x_490);
lean_dec(x_487);
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_488);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; size_t x_494; size_t x_495; 
x_492 = lean_ctor_get(x_486, 1);
lean_inc(x_492);
lean_dec(x_486);
x_493 = lean_ctor_get(x_487, 0);
lean_inc(x_493);
lean_dec(x_487);
x_494 = 1;
x_495 = lean_usize_add(x_6, x_494);
x_6 = x_495;
x_7 = x_493;
x_15 = x_492;
goto _start;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_497 = lean_ctor_get(x_486, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_486, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_499 = x_486;
} else {
 lean_dec_ref(x_486);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; uint8_t x_502; 
x_501 = lean_array_get_size(x_2);
x_502 = lean_nat_dec_lt(x_463, x_501);
lean_dec(x_501);
if (x_502 == 0)
{
lean_object* x_503; uint8_t x_504; uint8_t x_505; uint8_t x_506; lean_object* x_507; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_460);
lean_free_object(x_19);
lean_free_object(x_7);
x_503 = lean_box(0);
x_504 = lean_unbox(x_459);
lean_dec(x_459);
x_505 = lean_unbox(x_461);
lean_dec(x_461);
x_506 = lean_unbox(x_464);
lean_dec(x_464);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_507 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_480, x_477, x_18, x_28, x_458, x_504, x_505, x_463, x_506, x_503, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_510 = x_507;
} else {
 lean_dec_ref(x_507);
 x_510 = lean_box(0);
}
x_511 = lean_ctor_get(x_508, 0);
lean_inc(x_511);
lean_dec(x_508);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_509);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; size_t x_515; size_t x_516; 
x_513 = lean_ctor_get(x_507, 1);
lean_inc(x_513);
lean_dec(x_507);
x_514 = lean_ctor_get(x_508, 0);
lean_inc(x_514);
lean_dec(x_508);
x_515 = 1;
x_516 = lean_usize_add(x_6, x_515);
x_6 = x_516;
x_7 = x_514;
x_15 = x_513;
goto _start;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_518 = lean_ctor_get(x_507, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_507, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_520 = x_507;
} else {
 lean_dec_ref(x_507);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
else
{
lean_object* x_522; uint8_t x_523; 
x_522 = lean_array_fget(x_2, x_463);
x_523 = l_Lean_Meta_ParamInfo_isInstImplicit(x_522);
lean_dec(x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; uint8_t x_526; uint8_t x_527; lean_object* x_528; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_460);
lean_free_object(x_19);
lean_free_object(x_7);
x_524 = lean_box(0);
x_525 = lean_unbox(x_459);
lean_dec(x_459);
x_526 = lean_unbox(x_461);
lean_dec(x_461);
x_527 = lean_unbox(x_464);
lean_dec(x_464);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_528 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_480, x_477, x_18, x_28, x_458, x_525, x_526, x_463, x_527, x_524, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
x_532 = lean_ctor_get(x_529, 0);
lean_inc(x_532);
lean_dec(x_529);
if (lean_is_scalar(x_531)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_531;
}
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_530);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; size_t x_536; size_t x_537; 
x_534 = lean_ctor_get(x_528, 1);
lean_inc(x_534);
lean_dec(x_528);
x_535 = lean_ctor_get(x_529, 0);
lean_inc(x_535);
lean_dec(x_529);
x_536 = 1;
x_537 = lean_usize_add(x_6, x_536);
x_6 = x_537;
x_7 = x_535;
x_15 = x_534;
goto _start;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_539 = lean_ctor_get(x_528, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_528, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_541 = x_528;
} else {
 lean_dec_ref(x_528);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; size_t x_549; size_t x_550; 
x_543 = lean_array_push(x_458, x_18);
x_544 = lean_nat_add(x_463, x_478);
lean_dec(x_463);
if (lean_is_scalar(x_465)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_465;
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_464);
if (lean_is_scalar(x_462)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_462;
}
lean_ctor_set(x_546, 0, x_461);
lean_ctor_set(x_546, 1, x_545);
if (lean_is_scalar(x_460)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_460;
}
lean_ctor_set(x_547, 0, x_459);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_543);
lean_ctor_set(x_548, 1, x_547);
lean_ctor_set(x_19, 1, x_548);
lean_ctor_set(x_7, 0, x_480);
x_549 = 1;
x_550 = lean_usize_add(x_6, x_549);
x_6 = x_550;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
x_552 = lean_ctor_get(x_19, 0);
lean_inc(x_552);
lean_dec(x_19);
x_553 = lean_ctor_get(x_20, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_554 = x_20;
} else {
 lean_dec_ref(x_20);
 x_554 = lean_box(0);
}
x_555 = lean_ctor_get(x_21, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_556 = x_21;
} else {
 lean_dec_ref(x_21);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_22, 0);
lean_inc(x_557);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_558 = x_22;
} else {
 lean_dec_ref(x_22);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_23, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_23, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_561 = x_23;
} else {
 lean_dec_ref(x_23);
 x_561 = lean_box(0);
}
x_562 = lean_ctor_get(x_25, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_25, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_25, 2);
lean_inc(x_564);
x_565 = lean_nat_dec_lt(x_563, x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_561)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_561;
}
lean_ctor_set(x_566, 0, x_559);
lean_ctor_set(x_566, 1, x_560);
if (lean_is_scalar(x_558)) {
 x_567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_567 = x_558;
}
lean_ctor_set(x_567, 0, x_557);
lean_ctor_set(x_567, 1, x_566);
if (lean_is_scalar(x_556)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_556;
}
lean_ctor_set(x_568, 0, x_555);
lean_ctor_set(x_568, 1, x_567);
if (lean_is_scalar(x_554)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_554;
}
lean_ctor_set(x_569, 0, x_553);
lean_ctor_set(x_569, 1, x_568);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_552);
lean_ctor_set(x_570, 1, x_569);
lean_ctor_set(x_7, 1, x_570);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_7);
lean_ctor_set(x_571, 1, x_15);
return x_571;
}
else
{
lean_object* x_572; lean_object* x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_572 = x_25;
} else {
 lean_dec_ref(x_25);
 x_572 = lean_box(0);
}
x_573 = lean_array_fget(x_562, x_563);
x_574 = lean_unbox(x_573);
lean_dec(x_573);
x_575 = lean_unsigned_to_nat(1u);
x_576 = lean_nat_add(x_563, x_575);
lean_dec(x_563);
if (lean_is_scalar(x_572)) {
 x_577 = lean_alloc_ctor(0, 3, 0);
} else {
 x_577 = x_572;
}
lean_ctor_set(x_577, 0, x_562);
lean_ctor_set(x_577, 1, x_576);
lean_ctor_set(x_577, 2, x_564);
x_578 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_578 == 0)
{
lean_object* x_579; uint8_t x_580; uint8_t x_581; uint8_t x_582; lean_object* x_583; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_554);
lean_free_object(x_7);
x_579 = lean_box(0);
x_580 = lean_unbox(x_555);
lean_dec(x_555);
x_581 = lean_unbox(x_557);
lean_dec(x_557);
x_582 = lean_unbox(x_560);
lean_dec(x_560);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_583 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_577, x_574, x_18, x_552, x_553, x_580, x_581, x_559, x_582, x_579, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_586 = x_583;
} else {
 lean_dec_ref(x_583);
 x_586 = lean_box(0);
}
x_587 = lean_ctor_get(x_584, 0);
lean_inc(x_587);
lean_dec(x_584);
if (lean_is_scalar(x_586)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_586;
}
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_585);
return x_588;
}
else
{
lean_object* x_589; lean_object* x_590; size_t x_591; size_t x_592; 
x_589 = lean_ctor_get(x_583, 1);
lean_inc(x_589);
lean_dec(x_583);
x_590 = lean_ctor_get(x_584, 0);
lean_inc(x_590);
lean_dec(x_584);
x_591 = 1;
x_592 = lean_usize_add(x_6, x_591);
x_6 = x_592;
x_7 = x_590;
x_15 = x_589;
goto _start;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_594 = lean_ctor_get(x_583, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_583, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_596 = x_583;
} else {
 lean_dec_ref(x_583);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
else
{
lean_object* x_598; uint8_t x_599; 
x_598 = lean_array_get_size(x_2);
x_599 = lean_nat_dec_lt(x_559, x_598);
lean_dec(x_598);
if (x_599 == 0)
{
lean_object* x_600; uint8_t x_601; uint8_t x_602; uint8_t x_603; lean_object* x_604; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_554);
lean_free_object(x_7);
x_600 = lean_box(0);
x_601 = lean_unbox(x_555);
lean_dec(x_555);
x_602 = lean_unbox(x_557);
lean_dec(x_557);
x_603 = lean_unbox(x_560);
lean_dec(x_560);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_604 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_577, x_574, x_18, x_552, x_553, x_601, x_602, x_559, x_603, x_600, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_607 = x_604;
} else {
 lean_dec_ref(x_604);
 x_607 = lean_box(0);
}
x_608 = lean_ctor_get(x_605, 0);
lean_inc(x_608);
lean_dec(x_605);
if (lean_is_scalar(x_607)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_607;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_606);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; size_t x_612; size_t x_613; 
x_610 = lean_ctor_get(x_604, 1);
lean_inc(x_610);
lean_dec(x_604);
x_611 = lean_ctor_get(x_605, 0);
lean_inc(x_611);
lean_dec(x_605);
x_612 = 1;
x_613 = lean_usize_add(x_6, x_612);
x_6 = x_613;
x_7 = x_611;
x_15 = x_610;
goto _start;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_615 = lean_ctor_get(x_604, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_604, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_617 = x_604;
} else {
 lean_dec_ref(x_604);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_615);
lean_ctor_set(x_618, 1, x_616);
return x_618;
}
}
else
{
lean_object* x_619; uint8_t x_620; 
x_619 = lean_array_fget(x_2, x_559);
x_620 = l_Lean_Meta_ParamInfo_isInstImplicit(x_619);
lean_dec(x_619);
if (x_620 == 0)
{
lean_object* x_621; uint8_t x_622; uint8_t x_623; uint8_t x_624; lean_object* x_625; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_554);
lean_free_object(x_7);
x_621 = lean_box(0);
x_622 = lean_unbox(x_555);
lean_dec(x_555);
x_623 = lean_unbox(x_557);
lean_dec(x_557);
x_624 = lean_unbox(x_560);
lean_dec(x_560);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_625 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_577, x_574, x_18, x_552, x_553, x_622, x_623, x_559, x_624, x_621, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_628 = x_625;
} else {
 lean_dec_ref(x_625);
 x_628 = lean_box(0);
}
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
lean_dec(x_626);
if (lean_is_scalar(x_628)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_628;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_627);
return x_630;
}
else
{
lean_object* x_631; lean_object* x_632; size_t x_633; size_t x_634; 
x_631 = lean_ctor_get(x_625, 1);
lean_inc(x_631);
lean_dec(x_625);
x_632 = lean_ctor_get(x_626, 0);
lean_inc(x_632);
lean_dec(x_626);
x_633 = 1;
x_634 = lean_usize_add(x_6, x_633);
x_6 = x_634;
x_7 = x_632;
x_15 = x_631;
goto _start;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_636 = lean_ctor_get(x_625, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_625, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_638 = x_625;
} else {
 lean_dec_ref(x_625);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; size_t x_647; size_t x_648; 
x_640 = lean_array_push(x_553, x_18);
x_641 = lean_nat_add(x_559, x_575);
lean_dec(x_559);
if (lean_is_scalar(x_561)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_561;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_560);
if (lean_is_scalar(x_558)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_558;
}
lean_ctor_set(x_643, 0, x_557);
lean_ctor_set(x_643, 1, x_642);
if (lean_is_scalar(x_556)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_556;
}
lean_ctor_set(x_644, 0, x_555);
lean_ctor_set(x_644, 1, x_643);
if (lean_is_scalar(x_554)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_554;
}
lean_ctor_set(x_645, 0, x_640);
lean_ctor_set(x_645, 1, x_644);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_552);
lean_ctor_set(x_646, 1, x_645);
lean_ctor_set(x_7, 1, x_646);
lean_ctor_set(x_7, 0, x_577);
x_647 = 1;
x_648 = lean_usize_add(x_6, x_647);
x_6 = x_648;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_650 = lean_ctor_get(x_7, 0);
lean_inc(x_650);
lean_dec(x_7);
x_651 = lean_ctor_get(x_19, 0);
lean_inc(x_651);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_652 = x_19;
} else {
 lean_dec_ref(x_19);
 x_652 = lean_box(0);
}
x_653 = lean_ctor_get(x_20, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_654 = x_20;
} else {
 lean_dec_ref(x_20);
 x_654 = lean_box(0);
}
x_655 = lean_ctor_get(x_21, 0);
lean_inc(x_655);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_656 = x_21;
} else {
 lean_dec_ref(x_21);
 x_656 = lean_box(0);
}
x_657 = lean_ctor_get(x_22, 0);
lean_inc(x_657);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_658 = x_22;
} else {
 lean_dec_ref(x_22);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_23, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_23, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_661 = x_23;
} else {
 lean_dec_ref(x_23);
 x_661 = lean_box(0);
}
x_662 = lean_ctor_get(x_650, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_650, 1);
lean_inc(x_663);
x_664 = lean_ctor_get(x_650, 2);
lean_inc(x_664);
x_665 = lean_nat_dec_lt(x_663, x_664);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_661)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_661;
}
lean_ctor_set(x_666, 0, x_659);
lean_ctor_set(x_666, 1, x_660);
if (lean_is_scalar(x_658)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_658;
}
lean_ctor_set(x_667, 0, x_657);
lean_ctor_set(x_667, 1, x_666);
if (lean_is_scalar(x_656)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_656;
}
lean_ctor_set(x_668, 0, x_655);
lean_ctor_set(x_668, 1, x_667);
if (lean_is_scalar(x_654)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_654;
}
lean_ctor_set(x_669, 0, x_653);
lean_ctor_set(x_669, 1, x_668);
if (lean_is_scalar(x_652)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_652;
}
lean_ctor_set(x_670, 0, x_651);
lean_ctor_set(x_670, 1, x_669);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_650);
lean_ctor_set(x_671, 1, x_670);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_15);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; uint8_t x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; 
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 lean_ctor_release(x_650, 2);
 x_673 = x_650;
} else {
 lean_dec_ref(x_650);
 x_673 = lean_box(0);
}
x_674 = lean_array_fget(x_662, x_663);
x_675 = lean_unbox(x_674);
lean_dec(x_674);
x_676 = lean_unsigned_to_nat(1u);
x_677 = lean_nat_add(x_663, x_676);
lean_dec(x_663);
if (lean_is_scalar(x_673)) {
 x_678 = lean_alloc_ctor(0, 3, 0);
} else {
 x_678 = x_673;
}
lean_ctor_set(x_678, 0, x_662);
lean_ctor_set(x_678, 1, x_677);
lean_ctor_set(x_678, 2, x_664);
x_679 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
if (x_679 == 0)
{
lean_object* x_680; uint8_t x_681; uint8_t x_682; uint8_t x_683; lean_object* x_684; 
lean_dec(x_661);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
lean_dec(x_652);
x_680 = lean_box(0);
x_681 = lean_unbox(x_655);
lean_dec(x_655);
x_682 = lean_unbox(x_657);
lean_dec(x_657);
x_683 = lean_unbox(x_660);
lean_dec(x_660);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_684 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_678, x_675, x_18, x_651, x_653, x_681, x_682, x_659, x_683, x_680, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_687 = x_684;
} else {
 lean_dec_ref(x_684);
 x_687 = lean_box(0);
}
x_688 = lean_ctor_get(x_685, 0);
lean_inc(x_688);
lean_dec(x_685);
if (lean_is_scalar(x_687)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_687;
}
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_686);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; size_t x_692; size_t x_693; 
x_690 = lean_ctor_get(x_684, 1);
lean_inc(x_690);
lean_dec(x_684);
x_691 = lean_ctor_get(x_685, 0);
lean_inc(x_691);
lean_dec(x_685);
x_692 = 1;
x_693 = lean_usize_add(x_6, x_692);
x_6 = x_693;
x_7 = x_691;
x_15 = x_690;
goto _start;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_695 = lean_ctor_get(x_684, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_684, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_697 = x_684;
} else {
 lean_dec_ref(x_684);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
lean_object* x_699; uint8_t x_700; 
x_699 = lean_array_get_size(x_2);
x_700 = lean_nat_dec_lt(x_659, x_699);
lean_dec(x_699);
if (x_700 == 0)
{
lean_object* x_701; uint8_t x_702; uint8_t x_703; uint8_t x_704; lean_object* x_705; 
lean_dec(x_661);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
lean_dec(x_652);
x_701 = lean_box(0);
x_702 = lean_unbox(x_655);
lean_dec(x_655);
x_703 = lean_unbox(x_657);
lean_dec(x_657);
x_704 = lean_unbox(x_660);
lean_dec(x_660);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_705 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_678, x_675, x_18, x_651, x_653, x_702, x_703, x_659, x_704, x_701, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; 
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_708 = x_705;
} else {
 lean_dec_ref(x_705);
 x_708 = lean_box(0);
}
x_709 = lean_ctor_get(x_706, 0);
lean_inc(x_709);
lean_dec(x_706);
if (lean_is_scalar(x_708)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_708;
}
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_707);
return x_710;
}
else
{
lean_object* x_711; lean_object* x_712; size_t x_713; size_t x_714; 
x_711 = lean_ctor_get(x_705, 1);
lean_inc(x_711);
lean_dec(x_705);
x_712 = lean_ctor_get(x_706, 0);
lean_inc(x_712);
lean_dec(x_706);
x_713 = 1;
x_714 = lean_usize_add(x_6, x_713);
x_6 = x_714;
x_7 = x_712;
x_15 = x_711;
goto _start;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_716 = lean_ctor_get(x_705, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_705, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_718 = x_705;
} else {
 lean_dec_ref(x_705);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
}
else
{
lean_object* x_720; uint8_t x_721; 
x_720 = lean_array_fget(x_2, x_659);
x_721 = l_Lean_Meta_ParamInfo_isInstImplicit(x_720);
lean_dec(x_720);
if (x_721 == 0)
{
lean_object* x_722; uint8_t x_723; uint8_t x_724; uint8_t x_725; lean_object* x_726; 
lean_dec(x_661);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
lean_dec(x_652);
x_722 = lean_box(0);
x_723 = lean_unbox(x_655);
lean_dec(x_655);
x_724 = lean_unbox(x_657);
lean_dec(x_657);
x_725 = lean_unbox(x_660);
lean_dec(x_660);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_726 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_678, x_675, x_18, x_651, x_653, x_723, x_724, x_659, x_725, x_722, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_729 = x_726;
} else {
 lean_dec_ref(x_726);
 x_729 = lean_box(0);
}
x_730 = lean_ctor_get(x_727, 0);
lean_inc(x_730);
lean_dec(x_727);
if (lean_is_scalar(x_729)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_729;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_728);
return x_731;
}
else
{
lean_object* x_732; lean_object* x_733; size_t x_734; size_t x_735; 
x_732 = lean_ctor_get(x_726, 1);
lean_inc(x_732);
lean_dec(x_726);
x_733 = lean_ctor_get(x_727, 0);
lean_inc(x_733);
lean_dec(x_727);
x_734 = 1;
x_735 = lean_usize_add(x_6, x_734);
x_6 = x_735;
x_7 = x_733;
x_15 = x_732;
goto _start;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_737 = lean_ctor_get(x_726, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_726, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_739 = x_726;
} else {
 lean_dec_ref(x_726);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; size_t x_749; size_t x_750; 
x_741 = lean_array_push(x_653, x_18);
x_742 = lean_nat_add(x_659, x_676);
lean_dec(x_659);
if (lean_is_scalar(x_661)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_661;
}
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_660);
if (lean_is_scalar(x_658)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_658;
}
lean_ctor_set(x_744, 0, x_657);
lean_ctor_set(x_744, 1, x_743);
if (lean_is_scalar(x_656)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_656;
}
lean_ctor_set(x_745, 0, x_655);
lean_ctor_set(x_745, 1, x_744);
if (lean_is_scalar(x_654)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_654;
}
lean_ctor_set(x_746, 0, x_741);
lean_ctor_set(x_746, 1, x_745);
if (lean_is_scalar(x_652)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_652;
}
lean_ctor_set(x_747, 0, x_651);
lean_ctor_set(x_747, 1, x_746);
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_678);
lean_ctor_set(x_748, 1, x_747);
x_749 = 1;
x_750 = lean_usize_add(x_6, x_749);
x_6 = x_750;
x_7 = x_748;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_8);
x_17 = l_Lean_Expr_app___override(x_5, x_8);
x_18 = lean_array_push(x_6, x_8);
x_19 = l_Lean_Expr_bindingBody_x21(x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(628u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_17 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_33, 2);
lean_inc(x_49);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_17);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_27);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_18 = x_52;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = lean_ctor_get(x_33, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_33, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_33, 0);
lean_dec(x_56);
x_57 = lean_array_fget(x_47, x_48);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_48, x_59);
lean_dec(x_48);
lean_ctor_set(x_33, 1, x_60);
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_36, 2);
lean_inc(x_63);
x_64 = lean_nat_dec_lt(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_17);
lean_inc(x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_27);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_18 = x_66;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_36, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_36, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_36, 0);
lean_dec(x_70);
x_71 = lean_array_fget(x_61, x_62);
x_72 = lean_nat_add(x_62, x_59);
lean_dec(x_62);
lean_ctor_set(x_36, 1, x_72);
lean_inc(x_17);
x_73 = l_Lean_Expr_app___override(x_42, x_17);
x_74 = l_Lean_Expr_bindingBody_x21(x_46);
lean_dec(x_46);
x_75 = lean_box(x_58);
switch (lean_obj_tag(x_75)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_17);
x_76 = lean_array_push(x_45, x_71);
lean_ctor_set(x_31, 1, x_74);
lean_ctor_set(x_31, 0, x_76);
lean_ctor_set(x_30, 0, x_73);
lean_inc(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_27);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_18 = x_78;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_71);
lean_inc(x_17);
x_79 = lean_array_push(x_45, x_17);
x_80 = lean_array_get_size(x_1);
x_81 = lean_nat_dec_lt(x_39, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = l_Lean_Meta_Simp_instInhabitedResult;
x_83 = l_outOfBounds___rarg(x_82);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_83);
x_84 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_83, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_nat_add(x_39, x_59);
lean_dec(x_39);
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec(x_83);
lean_inc(x_85);
lean_inc(x_88);
x_89 = l_Lean_mkAppB(x_73, x_88, x_85);
x_90 = lean_array_push(x_79, x_88);
x_91 = lean_array_push(x_90, x_85);
x_92 = l_Lean_Expr_bindingBody_x21(x_74);
lean_dec(x_74);
x_93 = l_Lean_Expr_bindingBody_x21(x_92);
lean_dec(x_92);
lean_ctor_set(x_31, 1, x_93);
lean_ctor_set(x_31, 0, x_91);
lean_ctor_set(x_30, 0, x_89);
lean_ctor_set(x_29, 0, x_87);
lean_inc(x_2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_94, 1, x_27);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_18 = x_95;
x_19 = x_86;
goto block_26;
}
else
{
uint8_t x_96; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
return x_84;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_84, 0);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_84);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_array_fget(x_1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_100);
x_101 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_100, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_nat_add(x_39, x_59);
lean_dec(x_39);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
lean_inc(x_102);
lean_inc(x_105);
x_106 = l_Lean_mkAppB(x_73, x_105, x_102);
x_107 = lean_array_push(x_79, x_105);
x_108 = lean_array_push(x_107, x_102);
x_109 = l_Lean_Expr_bindingBody_x21(x_74);
lean_dec(x_74);
x_110 = l_Lean_Expr_bindingBody_x21(x_109);
lean_dec(x_109);
lean_ctor_set(x_31, 1, x_110);
lean_ctor_set(x_31, 0, x_108);
lean_ctor_set(x_30, 0, x_106);
lean_ctor_set(x_29, 0, x_104);
lean_inc(x_2);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_27);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_18 = x_112;
x_19 = x_103;
goto block_26;
}
else
{
uint8_t x_113; 
lean_dec(x_100);
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_101);
if (x_113 == 0)
{
return x_101;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_101, 0);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_101);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
case 3:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_71);
x_117 = lean_array_push(x_45, x_17);
lean_ctor_set(x_31, 1, x_74);
lean_ctor_set(x_31, 0, x_117);
lean_ctor_set(x_30, 0, x_73);
lean_inc(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_2);
lean_ctor_set(x_118, 1, x_27);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_18 = x_119;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_71);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_120 = lean_array_push(x_45, x_17);
x_121 = l_Lean_Expr_bindingDomain_x21(x_74);
x_122 = lean_expr_instantiate_rev(x_121, x_120);
lean_dec(x_121);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_123 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_122);
x_126 = l_Lean_Meta_isExprDefEq(x_124, x_122, x_10, x_11, x_12, x_13, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_17);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_122);
x_131 = l_Lean_Meta_trySynthInstance(x_122, x_130, x_10, x_11, x_12, x_13, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_122);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_2);
x_135 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_33, x_36, x_2, x_73, x_120, x_74, x_134, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_133);
lean_dec(x_74);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_18 = x_136;
x_19 = x_137;
goto block_26;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_132);
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
lean_dec(x_131);
x_139 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_140 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_139, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_122);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_box(0);
x_145 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_130, x_120, x_74, x_73, x_39, x_33, x_36, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_18 = x_146;
x_19 = x_147;
goto block_26;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_140);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_149 = lean_ctor_get(x_140, 1);
x_150 = lean_ctor_get(x_140, 0);
lean_dec(x_150);
x_151 = l_Lean_indentExpr(x_122);
x_152 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
lean_ctor_set_tag(x_140, 7);
lean_ctor_set(x_140, 1, x_151);
lean_ctor_set(x_140, 0, x_152);
x_153 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_140);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_139, x_154, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_149);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_130, x_120, x_74, x_73, x_39, x_33, x_36, x_156, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_157);
lean_dec(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_18 = x_159;
x_19 = x_160;
goto block_26;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_161 = lean_ctor_get(x_140, 1);
lean_inc(x_161);
lean_dec(x_140);
x_162 = l_Lean_indentExpr(x_122);
x_163 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_139, x_166, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_161);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_130, x_120, x_74, x_73, x_39, x_33, x_36, x_168, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_169);
lean_dec(x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_18 = x_171;
x_19 = x_172;
goto block_26;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_173 = !lean_is_exclusive(x_131);
if (x_173 == 0)
{
return x_131;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_131, 0);
x_175 = lean_ctor_get(x_131, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_131);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_122);
x_177 = lean_ctor_get(x_126, 1);
lean_inc(x_177);
lean_dec(x_126);
lean_inc(x_2);
x_178 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_33, x_36, x_2, x_73, x_120, x_74, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_177);
lean_dec(x_74);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_18 = x_179;
x_19 = x_180;
goto block_26;
}
}
else
{
uint8_t x_181; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_126);
if (x_181 == 0)
{
return x_126;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_126, 0);
x_183 = lean_ctor_get(x_126, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_126);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_123);
if (x_185 == 0)
{
return x_123;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_123, 0);
x_187 = lean_ctor_get(x_123, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_123);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
default: 
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_17);
x_189 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_190 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_189, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
lean_ctor_set(x_31, 1, x_74);
lean_ctor_set(x_30, 0, x_73);
lean_inc(x_2);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_2);
lean_ctor_set(x_192, 1, x_27);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_18 = x_193;
x_19 = x_191;
goto block_26;
}
else
{
uint8_t x_194; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_36);
lean_dec(x_33);
lean_free_object(x_31);
lean_dec(x_45);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_190);
if (x_194 == 0)
{
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 0);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_190);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_36);
x_198 = lean_array_fget(x_61, x_62);
x_199 = lean_nat_add(x_62, x_59);
lean_dec(x_62);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_61);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_63);
lean_inc(x_17);
x_201 = l_Lean_Expr_app___override(x_42, x_17);
x_202 = l_Lean_Expr_bindingBody_x21(x_46);
lean_dec(x_46);
x_203 = lean_box(x_58);
switch (lean_obj_tag(x_203)) {
case 0:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_17);
x_204 = lean_array_push(x_45, x_198);
lean_ctor_set(x_31, 1, x_202);
lean_ctor_set(x_31, 0, x_204);
lean_ctor_set(x_30, 0, x_201);
lean_ctor_set(x_27, 0, x_200);
lean_inc(x_2);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_2);
lean_ctor_set(x_205, 1, x_27);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_18 = x_206;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_198);
lean_inc(x_17);
x_207 = lean_array_push(x_45, x_17);
x_208 = lean_array_get_size(x_1);
x_209 = lean_nat_dec_lt(x_39, x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = l_Lean_Meta_Simp_instInhabitedResult;
x_211 = l_outOfBounds___rarg(x_210);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_211);
x_212 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_211, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_nat_add(x_39, x_59);
lean_dec(x_39);
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
lean_dec(x_211);
lean_inc(x_213);
lean_inc(x_216);
x_217 = l_Lean_mkAppB(x_201, x_216, x_213);
x_218 = lean_array_push(x_207, x_216);
x_219 = lean_array_push(x_218, x_213);
x_220 = l_Lean_Expr_bindingBody_x21(x_202);
lean_dec(x_202);
x_221 = l_Lean_Expr_bindingBody_x21(x_220);
lean_dec(x_220);
lean_ctor_set(x_31, 1, x_221);
lean_ctor_set(x_31, 0, x_219);
lean_ctor_set(x_30, 0, x_217);
lean_ctor_set(x_29, 0, x_215);
lean_ctor_set(x_27, 0, x_200);
lean_inc(x_2);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_2);
lean_ctor_set(x_222, 1, x_27);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_18 = x_223;
x_19 = x_214;
goto block_26;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_211);
lean_dec(x_207);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_224 = lean_ctor_get(x_212, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_212, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_226 = x_212;
} else {
 lean_dec_ref(x_212);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_array_fget(x_1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_228);
x_229 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_228, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_nat_add(x_39, x_59);
lean_dec(x_39);
x_233 = lean_ctor_get(x_228, 0);
lean_inc(x_233);
lean_dec(x_228);
lean_inc(x_230);
lean_inc(x_233);
x_234 = l_Lean_mkAppB(x_201, x_233, x_230);
x_235 = lean_array_push(x_207, x_233);
x_236 = lean_array_push(x_235, x_230);
x_237 = l_Lean_Expr_bindingBody_x21(x_202);
lean_dec(x_202);
x_238 = l_Lean_Expr_bindingBody_x21(x_237);
lean_dec(x_237);
lean_ctor_set(x_31, 1, x_238);
lean_ctor_set(x_31, 0, x_236);
lean_ctor_set(x_30, 0, x_234);
lean_ctor_set(x_29, 0, x_232);
lean_ctor_set(x_27, 0, x_200);
lean_inc(x_2);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_2);
lean_ctor_set(x_239, 1, x_27);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_18 = x_240;
x_19 = x_231;
goto block_26;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_228);
lean_dec(x_207);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_241 = lean_ctor_get(x_229, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_229, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_243 = x_229;
} else {
 lean_dec_ref(x_229);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
case 3:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_198);
x_245 = lean_array_push(x_45, x_17);
lean_ctor_set(x_31, 1, x_202);
lean_ctor_set(x_31, 0, x_245);
lean_ctor_set(x_30, 0, x_201);
lean_ctor_set(x_27, 0, x_200);
lean_inc(x_2);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_2);
lean_ctor_set(x_246, 1, x_27);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_18 = x_247;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_198);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_248 = lean_array_push(x_45, x_17);
x_249 = l_Lean_Expr_bindingDomain_x21(x_202);
x_250 = lean_expr_instantiate_rev(x_249, x_248);
lean_dec(x_249);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_251 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_250);
x_254 = l_Lean_Meta_isExprDefEq(x_252, x_250, x_10, x_11, x_12, x_13, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_17);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_250);
x_259 = l_Lean_Meta_trySynthInstance(x_250, x_258, x_10, x_11, x_12, x_13, x_257);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 1)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_250);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_2);
x_263 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_33, x_200, x_2, x_201, x_248, x_202, x_262, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_261);
lean_dec(x_202);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_18 = x_264;
x_19 = x_265;
goto block_26;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
lean_dec(x_260);
x_266 = lean_ctor_get(x_259, 1);
lean_inc(x_266);
lean_dec(x_259);
x_267 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_268 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_267, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_266);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_unbox(x_269);
lean_dec(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_250);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_box(0);
x_273 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_258, x_248, x_202, x_201, x_39, x_33, x_200, x_272, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_271);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_18 = x_274;
x_19 = x_275;
goto block_26;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_276 = lean_ctor_get(x_268, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_277 = x_268;
} else {
 lean_dec_ref(x_268);
 x_277 = lean_box(0);
}
x_278 = l_Lean_indentExpr(x_250);
x_279 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_277)) {
 x_280 = lean_alloc_ctor(7, 2, 0);
} else {
 x_280 = x_277;
 lean_ctor_set_tag(x_280, 7);
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_267, x_282, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_276);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_258, x_248, x_202, x_201, x_39, x_33, x_200, x_284, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_285);
lean_dec(x_284);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_18 = x_287;
x_19 = x_288;
goto block_26;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_250);
lean_dec(x_248);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_289 = lean_ctor_get(x_259, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_259, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_291 = x_259;
} else {
 lean_dec_ref(x_259);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_250);
x_293 = lean_ctor_get(x_254, 1);
lean_inc(x_293);
lean_dec(x_254);
lean_inc(x_2);
x_294 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_33, x_200, x_2, x_201, x_248, x_202, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_293);
lean_dec(x_202);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_18 = x_295;
x_19 = x_296;
goto block_26;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_250);
lean_dec(x_248);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_297 = lean_ctor_get(x_254, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_254, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_299 = x_254;
} else {
 lean_dec_ref(x_254);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_250);
lean_dec(x_248);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_301 = lean_ctor_get(x_251, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_251, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_303 = x_251;
} else {
 lean_dec_ref(x_251);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
default: 
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_203);
lean_dec(x_198);
lean_dec(x_17);
x_305 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_306 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_305, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
lean_ctor_set(x_31, 1, x_202);
lean_ctor_set(x_30, 0, x_201);
lean_ctor_set(x_27, 0, x_200);
lean_inc(x_2);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_2);
lean_ctor_set(x_308, 1, x_27);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_18 = x_309;
x_19 = x_307;
goto block_26;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_33);
lean_free_object(x_31);
lean_dec(x_45);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_310 = lean_ctor_get(x_306, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_306, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_312 = x_306;
} else {
 lean_dec_ref(x_306);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
}
}
else
{
lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_33);
x_314 = lean_array_fget(x_47, x_48);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
x_316 = lean_unsigned_to_nat(1u);
x_317 = lean_nat_add(x_48, x_316);
lean_dec(x_48);
x_318 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_318, 0, x_47);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set(x_318, 2, x_49);
x_319 = lean_ctor_get(x_36, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_36, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_36, 2);
lean_inc(x_321);
x_322 = lean_nat_dec_lt(x_320, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_17);
lean_ctor_set(x_28, 0, x_318);
lean_inc(x_2);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_2);
lean_ctor_set(x_323, 1, x_27);
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_323);
x_18 = x_324;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_325 = x_36;
} else {
 lean_dec_ref(x_36);
 x_325 = lean_box(0);
}
x_326 = lean_array_fget(x_319, x_320);
x_327 = lean_nat_add(x_320, x_316);
lean_dec(x_320);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(0, 3, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_319);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_328, 2, x_321);
lean_inc(x_17);
x_329 = l_Lean_Expr_app___override(x_42, x_17);
x_330 = l_Lean_Expr_bindingBody_x21(x_46);
lean_dec(x_46);
x_331 = lean_box(x_315);
switch (lean_obj_tag(x_331)) {
case 0:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_17);
x_332 = lean_array_push(x_45, x_326);
lean_ctor_set(x_31, 1, x_330);
lean_ctor_set(x_31, 0, x_332);
lean_ctor_set(x_30, 0, x_329);
lean_ctor_set(x_28, 0, x_318);
lean_ctor_set(x_27, 0, x_328);
lean_inc(x_2);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_2);
lean_ctor_set(x_333, 1, x_27);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_18 = x_334;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_326);
lean_inc(x_17);
x_335 = lean_array_push(x_45, x_17);
x_336 = lean_array_get_size(x_1);
x_337 = lean_nat_dec_lt(x_39, x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = l_Lean_Meta_Simp_instInhabitedResult;
x_339 = l_outOfBounds___rarg(x_338);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_339);
x_340 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_339, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_nat_add(x_39, x_316);
lean_dec(x_39);
x_344 = lean_ctor_get(x_339, 0);
lean_inc(x_344);
lean_dec(x_339);
lean_inc(x_341);
lean_inc(x_344);
x_345 = l_Lean_mkAppB(x_329, x_344, x_341);
x_346 = lean_array_push(x_335, x_344);
x_347 = lean_array_push(x_346, x_341);
x_348 = l_Lean_Expr_bindingBody_x21(x_330);
lean_dec(x_330);
x_349 = l_Lean_Expr_bindingBody_x21(x_348);
lean_dec(x_348);
lean_ctor_set(x_31, 1, x_349);
lean_ctor_set(x_31, 0, x_347);
lean_ctor_set(x_30, 0, x_345);
lean_ctor_set(x_29, 0, x_343);
lean_ctor_set(x_28, 0, x_318);
lean_ctor_set(x_27, 0, x_328);
lean_inc(x_2);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_2);
lean_ctor_set(x_350, 1, x_27);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
x_18 = x_351;
x_19 = x_342;
goto block_26;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_352 = lean_ctor_get(x_340, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_354 = x_340;
} else {
 lean_dec_ref(x_340);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_array_fget(x_1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_356);
x_357 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_356, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_nat_add(x_39, x_316);
lean_dec(x_39);
x_361 = lean_ctor_get(x_356, 0);
lean_inc(x_361);
lean_dec(x_356);
lean_inc(x_358);
lean_inc(x_361);
x_362 = l_Lean_mkAppB(x_329, x_361, x_358);
x_363 = lean_array_push(x_335, x_361);
x_364 = lean_array_push(x_363, x_358);
x_365 = l_Lean_Expr_bindingBody_x21(x_330);
lean_dec(x_330);
x_366 = l_Lean_Expr_bindingBody_x21(x_365);
lean_dec(x_365);
lean_ctor_set(x_31, 1, x_366);
lean_ctor_set(x_31, 0, x_364);
lean_ctor_set(x_30, 0, x_362);
lean_ctor_set(x_29, 0, x_360);
lean_ctor_set(x_28, 0, x_318);
lean_ctor_set(x_27, 0, x_328);
lean_inc(x_2);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_2);
lean_ctor_set(x_367, 1, x_27);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_18 = x_368;
x_19 = x_359;
goto block_26;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_356);
lean_dec(x_335);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_369 = lean_ctor_get(x_357, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_357, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_371 = x_357;
} else {
 lean_dec_ref(x_357);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
}
case 3:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_326);
x_373 = lean_array_push(x_45, x_17);
lean_ctor_set(x_31, 1, x_330);
lean_ctor_set(x_31, 0, x_373);
lean_ctor_set(x_30, 0, x_329);
lean_ctor_set(x_28, 0, x_318);
lean_ctor_set(x_27, 0, x_328);
lean_inc(x_2);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_2);
lean_ctor_set(x_374, 1, x_27);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_18 = x_375;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_326);
lean_free_object(x_31);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_376 = lean_array_push(x_45, x_17);
x_377 = l_Lean_Expr_bindingDomain_x21(x_330);
x_378 = lean_expr_instantiate_rev(x_377, x_376);
lean_dec(x_377);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_379 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_378);
x_382 = l_Lean_Meta_isExprDefEq(x_380, x_378, x_10, x_11, x_12, x_13, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_17);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
x_386 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_378);
x_387 = l_Lean_Meta_trySynthInstance(x_378, x_386, x_10, x_11, x_12, x_13, x_385);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_obj_tag(x_388) == 1)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_378);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_388, 0);
lean_inc(x_390);
lean_dec(x_388);
lean_inc(x_2);
x_391 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_318, x_328, x_2, x_329, x_376, x_330, x_390, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_389);
lean_dec(x_330);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_18 = x_392;
x_19 = x_393;
goto block_26;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_388);
x_394 = lean_ctor_get(x_387, 1);
lean_inc(x_394);
lean_dec(x_387);
x_395 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_396 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_395, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_394);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_378);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = lean_box(0);
x_401 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_386, x_376, x_330, x_329, x_39, x_318, x_328, x_400, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_399);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_18 = x_402;
x_19 = x_403;
goto block_26;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_404 = lean_ctor_get(x_396, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_405 = x_396;
} else {
 lean_dec_ref(x_396);
 x_405 = lean_box(0);
}
x_406 = l_Lean_indentExpr(x_378);
x_407 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_405)) {
 x_408 = lean_alloc_ctor(7, 2, 0);
} else {
 x_408 = x_405;
 lean_ctor_set_tag(x_408, 7);
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_406);
x_409 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_395, x_410, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_404);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_386, x_376, x_330, x_329, x_39, x_318, x_328, x_412, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_413);
lean_dec(x_412);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_18 = x_415;
x_19 = x_416;
goto block_26;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_417 = lean_ctor_get(x_387, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_387, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_419 = x_387;
} else {
 lean_dec_ref(x_387);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_378);
x_421 = lean_ctor_get(x_382, 1);
lean_inc(x_421);
lean_dec(x_382);
lean_inc(x_2);
x_422 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_318, x_328, x_2, x_329, x_376, x_330, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_421);
lean_dec(x_330);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_18 = x_423;
x_19 = x_424;
goto block_26;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_425 = lean_ctor_get(x_382, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_382, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_427 = x_382;
} else {
 lean_dec_ref(x_382);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_429 = lean_ctor_get(x_379, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_379, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_431 = x_379;
} else {
 lean_dec_ref(x_379);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
default: 
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_331);
lean_dec(x_326);
lean_dec(x_17);
x_433 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_434 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_433, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
lean_ctor_set(x_31, 1, x_330);
lean_ctor_set(x_30, 0, x_329);
lean_ctor_set(x_28, 0, x_318);
lean_ctor_set(x_27, 0, x_328);
lean_inc(x_2);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_2);
lean_ctor_set(x_436, 1, x_27);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_436);
x_18 = x_437;
x_19 = x_435;
goto block_26;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_318);
lean_free_object(x_31);
lean_dec(x_45);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_438 = lean_ctor_get(x_434, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_434, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_440 = x_434;
} else {
 lean_dec_ref(x_434);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_442 = lean_ctor_get(x_31, 0);
x_443 = lean_ctor_get(x_31, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_31);
x_444 = lean_ctor_get(x_33, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_33, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_33, 2);
lean_inc(x_446);
x_447 = lean_nat_dec_lt(x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_17);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_442);
lean_ctor_set(x_448, 1, x_443);
lean_ctor_set(x_30, 1, x_448);
lean_inc(x_2);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_2);
lean_ctor_set(x_449, 1, x_27);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_449);
x_18 = x_450;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_451 = x_33;
} else {
 lean_dec_ref(x_33);
 x_451 = lean_box(0);
}
x_452 = lean_array_fget(x_444, x_445);
x_453 = lean_unbox(x_452);
lean_dec(x_452);
x_454 = lean_unsigned_to_nat(1u);
x_455 = lean_nat_add(x_445, x_454);
lean_dec(x_445);
if (lean_is_scalar(x_451)) {
 x_456 = lean_alloc_ctor(0, 3, 0);
} else {
 x_456 = x_451;
}
lean_ctor_set(x_456, 0, x_444);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_456, 2, x_446);
x_457 = lean_ctor_get(x_36, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_36, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_36, 2);
lean_inc(x_459);
x_460 = lean_nat_dec_lt(x_458, x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_17);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_442);
lean_ctor_set(x_461, 1, x_443);
lean_ctor_set(x_30, 1, x_461);
lean_ctor_set(x_28, 0, x_456);
lean_inc(x_2);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_2);
lean_ctor_set(x_462, 1, x_27);
x_463 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_18 = x_463;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_464 = x_36;
} else {
 lean_dec_ref(x_36);
 x_464 = lean_box(0);
}
x_465 = lean_array_fget(x_457, x_458);
x_466 = lean_nat_add(x_458, x_454);
lean_dec(x_458);
if (lean_is_scalar(x_464)) {
 x_467 = lean_alloc_ctor(0, 3, 0);
} else {
 x_467 = x_464;
}
lean_ctor_set(x_467, 0, x_457);
lean_ctor_set(x_467, 1, x_466);
lean_ctor_set(x_467, 2, x_459);
lean_inc(x_17);
x_468 = l_Lean_Expr_app___override(x_42, x_17);
x_469 = l_Lean_Expr_bindingBody_x21(x_443);
lean_dec(x_443);
x_470 = lean_box(x_453);
switch (lean_obj_tag(x_470)) {
case 0:
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_17);
x_471 = lean_array_push(x_442, x_465);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_469);
lean_ctor_set(x_30, 1, x_472);
lean_ctor_set(x_30, 0, x_468);
lean_ctor_set(x_28, 0, x_456);
lean_ctor_set(x_27, 0, x_467);
lean_inc(x_2);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_2);
lean_ctor_set(x_473, 1, x_27);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_18 = x_474;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; 
lean_dec(x_465);
lean_inc(x_17);
x_475 = lean_array_push(x_442, x_17);
x_476 = lean_array_get_size(x_1);
x_477 = lean_nat_dec_lt(x_39, x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = l_Lean_Meta_Simp_instInhabitedResult;
x_479 = l_outOfBounds___rarg(x_478);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_479);
x_480 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_479, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = lean_nat_add(x_39, x_454);
lean_dec(x_39);
x_484 = lean_ctor_get(x_479, 0);
lean_inc(x_484);
lean_dec(x_479);
lean_inc(x_481);
lean_inc(x_484);
x_485 = l_Lean_mkAppB(x_468, x_484, x_481);
x_486 = lean_array_push(x_475, x_484);
x_487 = lean_array_push(x_486, x_481);
x_488 = l_Lean_Expr_bindingBody_x21(x_469);
lean_dec(x_469);
x_489 = l_Lean_Expr_bindingBody_x21(x_488);
lean_dec(x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_489);
lean_ctor_set(x_30, 1, x_490);
lean_ctor_set(x_30, 0, x_485);
lean_ctor_set(x_29, 0, x_483);
lean_ctor_set(x_28, 0, x_456);
lean_ctor_set(x_27, 0, x_467);
lean_inc(x_2);
x_491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_491, 0, x_2);
lean_ctor_set(x_491, 1, x_27);
x_492 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_492, 0, x_491);
x_18 = x_492;
x_19 = x_482;
goto block_26;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_479);
lean_dec(x_475);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_493 = lean_ctor_get(x_480, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_480, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_495 = x_480;
} else {
 lean_dec_ref(x_480);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_array_fget(x_1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_497);
x_498 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_497, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_nat_add(x_39, x_454);
lean_dec(x_39);
x_502 = lean_ctor_get(x_497, 0);
lean_inc(x_502);
lean_dec(x_497);
lean_inc(x_499);
lean_inc(x_502);
x_503 = l_Lean_mkAppB(x_468, x_502, x_499);
x_504 = lean_array_push(x_475, x_502);
x_505 = lean_array_push(x_504, x_499);
x_506 = l_Lean_Expr_bindingBody_x21(x_469);
lean_dec(x_469);
x_507 = l_Lean_Expr_bindingBody_x21(x_506);
lean_dec(x_506);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_507);
lean_ctor_set(x_30, 1, x_508);
lean_ctor_set(x_30, 0, x_503);
lean_ctor_set(x_29, 0, x_501);
lean_ctor_set(x_28, 0, x_456);
lean_ctor_set(x_27, 0, x_467);
lean_inc(x_2);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_2);
lean_ctor_set(x_509, 1, x_27);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_18 = x_510;
x_19 = x_500;
goto block_26;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_497);
lean_dec(x_475);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_511 = lean_ctor_get(x_498, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_498, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_513 = x_498;
} else {
 lean_dec_ref(x_498);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
}
case 3:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_465);
x_515 = lean_array_push(x_442, x_17);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_469);
lean_ctor_set(x_30, 1, x_516);
lean_ctor_set(x_30, 0, x_468);
lean_ctor_set(x_28, 0, x_456);
lean_ctor_set(x_27, 0, x_467);
lean_inc(x_2);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_2);
lean_ctor_set(x_517, 1, x_27);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
x_18 = x_518;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_465);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_519 = lean_array_push(x_442, x_17);
x_520 = l_Lean_Expr_bindingDomain_x21(x_469);
x_521 = lean_expr_instantiate_rev(x_520, x_519);
lean_dec(x_520);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_522 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_521);
x_525 = l_Lean_Meta_isExprDefEq(x_523, x_521, x_10, x_11, x_12, x_13, x_524);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; uint8_t x_527; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_unbox(x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_17);
x_528 = lean_ctor_get(x_525, 1);
lean_inc(x_528);
lean_dec(x_525);
x_529 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_521);
x_530 = l_Lean_Meta_trySynthInstance(x_521, x_529, x_10, x_11, x_12, x_13, x_528);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
if (lean_obj_tag(x_531) == 1)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_521);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
lean_dec(x_531);
lean_inc(x_2);
x_534 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_456, x_467, x_2, x_468, x_519, x_469, x_533, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_532);
lean_dec(x_469);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_18 = x_535;
x_19 = x_536;
goto block_26;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
lean_dec(x_531);
x_537 = lean_ctor_get(x_530, 1);
lean_inc(x_537);
lean_dec(x_530);
x_538 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_539 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_538, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_537);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_unbox(x_540);
lean_dec(x_540);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_521);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = lean_box(0);
x_544 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_529, x_519, x_469, x_468, x_39, x_456, x_467, x_543, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_542);
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_18 = x_545;
x_19 = x_546;
goto block_26;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_547 = lean_ctor_get(x_539, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_548 = x_539;
} else {
 lean_dec_ref(x_539);
 x_548 = lean_box(0);
}
x_549 = l_Lean_indentExpr(x_521);
x_550 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_548)) {
 x_551 = lean_alloc_ctor(7, 2, 0);
} else {
 x_551 = x_548;
 lean_ctor_set_tag(x_551, 7);
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_549);
x_552 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_553 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
x_554 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_538, x_553, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_547);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_529, x_519, x_469, x_468, x_39, x_456, x_467, x_555, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_556);
lean_dec(x_555);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_18 = x_558;
x_19 = x_559;
goto block_26;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_560 = lean_ctor_get(x_530, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_530, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_562 = x_530;
} else {
 lean_dec_ref(x_530);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_560);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_521);
x_564 = lean_ctor_get(x_525, 1);
lean_inc(x_564);
lean_dec(x_525);
lean_inc(x_2);
x_565 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_456, x_467, x_2, x_468, x_519, x_469, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_564);
lean_dec(x_469);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
x_18 = x_566;
x_19 = x_567;
goto block_26;
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_568 = lean_ctor_get(x_525, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_525, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_570 = x_525;
} else {
 lean_dec_ref(x_525);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_572 = lean_ctor_get(x_522, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_522, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_574 = x_522;
} else {
 lean_dec_ref(x_522);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(1, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_572);
lean_ctor_set(x_575, 1, x_573);
return x_575;
}
}
default: 
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_470);
lean_dec(x_465);
lean_dec(x_17);
x_576 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_577 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_576, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_442);
lean_ctor_set(x_579, 1, x_469);
lean_ctor_set(x_30, 1, x_579);
lean_ctor_set(x_30, 0, x_468);
lean_ctor_set(x_28, 0, x_456);
lean_ctor_set(x_27, 0, x_467);
lean_inc(x_2);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_2);
lean_ctor_set(x_580, 1, x_27);
x_581 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_581, 0, x_580);
x_18 = x_581;
x_19 = x_578;
goto block_26;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_456);
lean_dec(x_442);
lean_free_object(x_30);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_582 = lean_ctor_get(x_577, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_577, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_584 = x_577;
} else {
 lean_dec_ref(x_577);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
}
}
}
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_586 = lean_ctor_get(x_30, 0);
lean_inc(x_586);
lean_dec(x_30);
x_587 = lean_ctor_get(x_31, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_31, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_589 = x_31;
} else {
 lean_dec_ref(x_31);
 x_589 = lean_box(0);
}
x_590 = lean_ctor_get(x_33, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_33, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_33, 2);
lean_inc(x_592);
x_593 = lean_nat_dec_lt(x_591, x_592);
if (x_593 == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_17);
if (lean_is_scalar(x_589)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_589;
}
lean_ctor_set(x_594, 0, x_587);
lean_ctor_set(x_594, 1, x_588);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_586);
lean_ctor_set(x_595, 1, x_594);
lean_ctor_set(x_29, 1, x_595);
lean_inc(x_2);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_2);
lean_ctor_set(x_596, 1, x_27);
x_597 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_597, 0, x_596);
x_18 = x_597;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_598 = x_33;
} else {
 lean_dec_ref(x_33);
 x_598 = lean_box(0);
}
x_599 = lean_array_fget(x_590, x_591);
x_600 = lean_unbox(x_599);
lean_dec(x_599);
x_601 = lean_unsigned_to_nat(1u);
x_602 = lean_nat_add(x_591, x_601);
lean_dec(x_591);
if (lean_is_scalar(x_598)) {
 x_603 = lean_alloc_ctor(0, 3, 0);
} else {
 x_603 = x_598;
}
lean_ctor_set(x_603, 0, x_590);
lean_ctor_set(x_603, 1, x_602);
lean_ctor_set(x_603, 2, x_592);
x_604 = lean_ctor_get(x_36, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_36, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_36, 2);
lean_inc(x_606);
x_607 = lean_nat_dec_lt(x_605, x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_17);
if (lean_is_scalar(x_589)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_589;
}
lean_ctor_set(x_608, 0, x_587);
lean_ctor_set(x_608, 1, x_588);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_586);
lean_ctor_set(x_609, 1, x_608);
lean_ctor_set(x_29, 1, x_609);
lean_ctor_set(x_28, 0, x_603);
lean_inc(x_2);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_2);
lean_ctor_set(x_610, 1, x_27);
x_611 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_611, 0, x_610);
x_18 = x_611;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_612 = x_36;
} else {
 lean_dec_ref(x_36);
 x_612 = lean_box(0);
}
x_613 = lean_array_fget(x_604, x_605);
x_614 = lean_nat_add(x_605, x_601);
lean_dec(x_605);
if (lean_is_scalar(x_612)) {
 x_615 = lean_alloc_ctor(0, 3, 0);
} else {
 x_615 = x_612;
}
lean_ctor_set(x_615, 0, x_604);
lean_ctor_set(x_615, 1, x_614);
lean_ctor_set(x_615, 2, x_606);
lean_inc(x_17);
x_616 = l_Lean_Expr_app___override(x_586, x_17);
x_617 = l_Lean_Expr_bindingBody_x21(x_588);
lean_dec(x_588);
x_618 = lean_box(x_600);
switch (lean_obj_tag(x_618)) {
case 0:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_17);
x_619 = lean_array_push(x_587, x_613);
if (lean_is_scalar(x_589)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_589;
}
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_617);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_616);
lean_ctor_set(x_621, 1, x_620);
lean_ctor_set(x_29, 1, x_621);
lean_ctor_set(x_28, 0, x_603);
lean_ctor_set(x_27, 0, x_615);
lean_inc(x_2);
x_622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_622, 0, x_2);
lean_ctor_set(x_622, 1, x_27);
x_623 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_623, 0, x_622);
x_18 = x_623;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_624; lean_object* x_625; uint8_t x_626; 
lean_dec(x_613);
lean_inc(x_17);
x_624 = lean_array_push(x_587, x_17);
x_625 = lean_array_get_size(x_1);
x_626 = lean_nat_dec_lt(x_39, x_625);
lean_dec(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = l_Lean_Meta_Simp_instInhabitedResult;
x_628 = l_outOfBounds___rarg(x_627);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_628);
x_629 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_628, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_nat_add(x_39, x_601);
lean_dec(x_39);
x_633 = lean_ctor_get(x_628, 0);
lean_inc(x_633);
lean_dec(x_628);
lean_inc(x_630);
lean_inc(x_633);
x_634 = l_Lean_mkAppB(x_616, x_633, x_630);
x_635 = lean_array_push(x_624, x_633);
x_636 = lean_array_push(x_635, x_630);
x_637 = l_Lean_Expr_bindingBody_x21(x_617);
lean_dec(x_617);
x_638 = l_Lean_Expr_bindingBody_x21(x_637);
lean_dec(x_637);
if (lean_is_scalar(x_589)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_589;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_638);
x_640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_640, 0, x_634);
lean_ctor_set(x_640, 1, x_639);
lean_ctor_set(x_29, 1, x_640);
lean_ctor_set(x_29, 0, x_632);
lean_ctor_set(x_28, 0, x_603);
lean_ctor_set(x_27, 0, x_615);
lean_inc(x_2);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_2);
lean_ctor_set(x_641, 1, x_27);
x_642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_18 = x_642;
x_19 = x_631;
goto block_26;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_628);
lean_dec(x_624);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_589);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_643 = lean_ctor_get(x_629, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_629, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 x_645 = x_629;
} else {
 lean_dec_ref(x_629);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_array_fget(x_1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_647);
x_648 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_647, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_651 = lean_nat_add(x_39, x_601);
lean_dec(x_39);
x_652 = lean_ctor_get(x_647, 0);
lean_inc(x_652);
lean_dec(x_647);
lean_inc(x_649);
lean_inc(x_652);
x_653 = l_Lean_mkAppB(x_616, x_652, x_649);
x_654 = lean_array_push(x_624, x_652);
x_655 = lean_array_push(x_654, x_649);
x_656 = l_Lean_Expr_bindingBody_x21(x_617);
lean_dec(x_617);
x_657 = l_Lean_Expr_bindingBody_x21(x_656);
lean_dec(x_656);
if (lean_is_scalar(x_589)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_589;
}
lean_ctor_set(x_658, 0, x_655);
lean_ctor_set(x_658, 1, x_657);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_653);
lean_ctor_set(x_659, 1, x_658);
lean_ctor_set(x_29, 1, x_659);
lean_ctor_set(x_29, 0, x_651);
lean_ctor_set(x_28, 0, x_603);
lean_ctor_set(x_27, 0, x_615);
lean_inc(x_2);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_2);
lean_ctor_set(x_660, 1, x_27);
x_661 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_661, 0, x_660);
x_18 = x_661;
x_19 = x_650;
goto block_26;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_647);
lean_dec(x_624);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_589);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_662 = lean_ctor_get(x_648, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_648, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_664 = x_648;
} else {
 lean_dec_ref(x_648);
 x_664 = lean_box(0);
}
if (lean_is_scalar(x_664)) {
 x_665 = lean_alloc_ctor(1, 2, 0);
} else {
 x_665 = x_664;
}
lean_ctor_set(x_665, 0, x_662);
lean_ctor_set(x_665, 1, x_663);
return x_665;
}
}
}
case 3:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_613);
x_666 = lean_array_push(x_587, x_17);
if (lean_is_scalar(x_589)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_589;
}
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_617);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_616);
lean_ctor_set(x_668, 1, x_667);
lean_ctor_set(x_29, 1, x_668);
lean_ctor_set(x_28, 0, x_603);
lean_ctor_set(x_27, 0, x_615);
lean_inc(x_2);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_2);
lean_ctor_set(x_669, 1, x_27);
x_670 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_670, 0, x_669);
x_18 = x_670;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_613);
lean_dec(x_589);
lean_free_object(x_29);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_671 = lean_array_push(x_587, x_17);
x_672 = l_Lean_Expr_bindingDomain_x21(x_617);
x_673 = lean_expr_instantiate_rev(x_672, x_671);
lean_dec(x_672);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_674 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_673);
x_677 = l_Lean_Meta_isExprDefEq(x_675, x_673, x_10, x_11, x_12, x_13, x_676);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; uint8_t x_679; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_unbox(x_678);
lean_dec(x_678);
if (x_679 == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_17);
x_680 = lean_ctor_get(x_677, 1);
lean_inc(x_680);
lean_dec(x_677);
x_681 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_673);
x_682 = l_Lean_Meta_trySynthInstance(x_673, x_681, x_10, x_11, x_12, x_13, x_680);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
if (lean_obj_tag(x_683) == 1)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_673);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
x_685 = lean_ctor_get(x_683, 0);
lean_inc(x_685);
lean_dec(x_683);
lean_inc(x_2);
x_686 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_603, x_615, x_2, x_616, x_671, x_617, x_685, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_684);
lean_dec(x_617);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec(x_686);
x_18 = x_687;
x_19 = x_688;
goto block_26;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
lean_dec(x_683);
x_689 = lean_ctor_get(x_682, 1);
lean_inc(x_689);
lean_dec(x_682);
x_690 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_691 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_690, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_689);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_unbox(x_692);
lean_dec(x_692);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_673);
x_694 = lean_ctor_get(x_691, 1);
lean_inc(x_694);
lean_dec(x_691);
x_695 = lean_box(0);
x_696 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_681, x_671, x_617, x_616, x_39, x_603, x_615, x_695, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_694);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_18 = x_697;
x_19 = x_698;
goto block_26;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_699 = lean_ctor_get(x_691, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_700 = x_691;
} else {
 lean_dec_ref(x_691);
 x_700 = lean_box(0);
}
x_701 = l_Lean_indentExpr(x_673);
x_702 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_700)) {
 x_703 = lean_alloc_ctor(7, 2, 0);
} else {
 x_703 = x_700;
 lean_ctor_set_tag(x_703, 7);
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
x_704 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_705 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_705, 0, x_703);
lean_ctor_set(x_705, 1, x_704);
x_706 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_690, x_705, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_699);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_681, x_671, x_617, x_616, x_39, x_603, x_615, x_707, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_708);
lean_dec(x_707);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_18 = x_710;
x_19 = x_711;
goto block_26;
}
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_712 = lean_ctor_get(x_682, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_682, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_714 = x_682;
} else {
 lean_dec_ref(x_682);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_712);
lean_ctor_set(x_715, 1, x_713);
return x_715;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_673);
x_716 = lean_ctor_get(x_677, 1);
lean_inc(x_716);
lean_dec(x_677);
lean_inc(x_2);
x_717 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_39, x_603, x_615, x_2, x_616, x_671, x_617, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_716);
lean_dec(x_617);
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_18 = x_718;
x_19 = x_719;
goto block_26;
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_720 = lean_ctor_get(x_677, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_677, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 lean_ctor_release(x_677, 1);
 x_722 = x_677;
} else {
 lean_dec_ref(x_677);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_720);
lean_ctor_set(x_723, 1, x_721);
return x_723;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_724 = lean_ctor_get(x_674, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_674, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_726 = x_674;
} else {
 lean_dec_ref(x_674);
 x_726 = lean_box(0);
}
if (lean_is_scalar(x_726)) {
 x_727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_727 = x_726;
}
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_725);
return x_727;
}
}
default: 
{
lean_object* x_728; lean_object* x_729; 
lean_dec(x_618);
lean_dec(x_613);
lean_dec(x_17);
x_728 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_729 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_728, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_730 = lean_ctor_get(x_729, 1);
lean_inc(x_730);
lean_dec(x_729);
if (lean_is_scalar(x_589)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_589;
}
lean_ctor_set(x_731, 0, x_587);
lean_ctor_set(x_731, 1, x_617);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_616);
lean_ctor_set(x_732, 1, x_731);
lean_ctor_set(x_29, 1, x_732);
lean_ctor_set(x_28, 0, x_603);
lean_ctor_set(x_27, 0, x_615);
lean_inc(x_2);
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_2);
lean_ctor_set(x_733, 1, x_27);
x_734 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_734, 0, x_733);
x_18 = x_734;
x_19 = x_730;
goto block_26;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_603);
lean_dec(x_589);
lean_dec(x_587);
lean_free_object(x_29);
lean_dec(x_39);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_735 = lean_ctor_get(x_729, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_729, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_737 = x_729;
} else {
 lean_dec_ref(x_729);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
}
}
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; 
x_739 = lean_ctor_get(x_29, 0);
lean_inc(x_739);
lean_dec(x_29);
x_740 = lean_ctor_get(x_30, 0);
lean_inc(x_740);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_741 = x_30;
} else {
 lean_dec_ref(x_30);
 x_741 = lean_box(0);
}
x_742 = lean_ctor_get(x_31, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_31, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_744 = x_31;
} else {
 lean_dec_ref(x_31);
 x_744 = lean_box(0);
}
x_745 = lean_ctor_get(x_33, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_33, 1);
lean_inc(x_746);
x_747 = lean_ctor_get(x_33, 2);
lean_inc(x_747);
x_748 = lean_nat_dec_lt(x_746, x_747);
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_17);
if (lean_is_scalar(x_744)) {
 x_749 = lean_alloc_ctor(0, 2, 0);
} else {
 x_749 = x_744;
}
lean_ctor_set(x_749, 0, x_742);
lean_ctor_set(x_749, 1, x_743);
if (lean_is_scalar(x_741)) {
 x_750 = lean_alloc_ctor(0, 2, 0);
} else {
 x_750 = x_741;
}
lean_ctor_set(x_750, 0, x_740);
lean_ctor_set(x_750, 1, x_749);
x_751 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_751, 0, x_739);
lean_ctor_set(x_751, 1, x_750);
lean_ctor_set(x_28, 1, x_751);
lean_inc(x_2);
x_752 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_752, 0, x_2);
lean_ctor_set(x_752, 1, x_27);
x_753 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_753, 0, x_752);
x_18 = x_753;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_754 = x_33;
} else {
 lean_dec_ref(x_33);
 x_754 = lean_box(0);
}
x_755 = lean_array_fget(x_745, x_746);
x_756 = lean_unbox(x_755);
lean_dec(x_755);
x_757 = lean_unsigned_to_nat(1u);
x_758 = lean_nat_add(x_746, x_757);
lean_dec(x_746);
if (lean_is_scalar(x_754)) {
 x_759 = lean_alloc_ctor(0, 3, 0);
} else {
 x_759 = x_754;
}
lean_ctor_set(x_759, 0, x_745);
lean_ctor_set(x_759, 1, x_758);
lean_ctor_set(x_759, 2, x_747);
x_760 = lean_ctor_get(x_36, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_36, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_36, 2);
lean_inc(x_762);
x_763 = lean_nat_dec_lt(x_761, x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_17);
if (lean_is_scalar(x_744)) {
 x_764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_764 = x_744;
}
lean_ctor_set(x_764, 0, x_742);
lean_ctor_set(x_764, 1, x_743);
if (lean_is_scalar(x_741)) {
 x_765 = lean_alloc_ctor(0, 2, 0);
} else {
 x_765 = x_741;
}
lean_ctor_set(x_765, 0, x_740);
lean_ctor_set(x_765, 1, x_764);
x_766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_766, 0, x_739);
lean_ctor_set(x_766, 1, x_765);
lean_ctor_set(x_28, 1, x_766);
lean_ctor_set(x_28, 0, x_759);
lean_inc(x_2);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_2);
lean_ctor_set(x_767, 1, x_27);
x_768 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_768, 0, x_767);
x_18 = x_768;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_769 = x_36;
} else {
 lean_dec_ref(x_36);
 x_769 = lean_box(0);
}
x_770 = lean_array_fget(x_760, x_761);
x_771 = lean_nat_add(x_761, x_757);
lean_dec(x_761);
if (lean_is_scalar(x_769)) {
 x_772 = lean_alloc_ctor(0, 3, 0);
} else {
 x_772 = x_769;
}
lean_ctor_set(x_772, 0, x_760);
lean_ctor_set(x_772, 1, x_771);
lean_ctor_set(x_772, 2, x_762);
lean_inc(x_17);
x_773 = l_Lean_Expr_app___override(x_740, x_17);
x_774 = l_Lean_Expr_bindingBody_x21(x_743);
lean_dec(x_743);
x_775 = lean_box(x_756);
switch (lean_obj_tag(x_775)) {
case 0:
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_17);
x_776 = lean_array_push(x_742, x_770);
if (lean_is_scalar(x_744)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_744;
}
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_774);
if (lean_is_scalar(x_741)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_741;
}
lean_ctor_set(x_778, 0, x_773);
lean_ctor_set(x_778, 1, x_777);
x_779 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_779, 0, x_739);
lean_ctor_set(x_779, 1, x_778);
lean_ctor_set(x_28, 1, x_779);
lean_ctor_set(x_28, 0, x_759);
lean_ctor_set(x_27, 0, x_772);
lean_inc(x_2);
x_780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_780, 0, x_2);
lean_ctor_set(x_780, 1, x_27);
x_781 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_781, 0, x_780);
x_18 = x_781;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_782; lean_object* x_783; uint8_t x_784; 
lean_dec(x_770);
lean_inc(x_17);
x_782 = lean_array_push(x_742, x_17);
x_783 = lean_array_get_size(x_1);
x_784 = lean_nat_dec_lt(x_739, x_783);
lean_dec(x_783);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = l_Lean_Meta_Simp_instInhabitedResult;
x_786 = l_outOfBounds___rarg(x_785);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_786);
x_787 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_786, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_790 = lean_nat_add(x_739, x_757);
lean_dec(x_739);
x_791 = lean_ctor_get(x_786, 0);
lean_inc(x_791);
lean_dec(x_786);
lean_inc(x_788);
lean_inc(x_791);
x_792 = l_Lean_mkAppB(x_773, x_791, x_788);
x_793 = lean_array_push(x_782, x_791);
x_794 = lean_array_push(x_793, x_788);
x_795 = l_Lean_Expr_bindingBody_x21(x_774);
lean_dec(x_774);
x_796 = l_Lean_Expr_bindingBody_x21(x_795);
lean_dec(x_795);
if (lean_is_scalar(x_744)) {
 x_797 = lean_alloc_ctor(0, 2, 0);
} else {
 x_797 = x_744;
}
lean_ctor_set(x_797, 0, x_794);
lean_ctor_set(x_797, 1, x_796);
if (lean_is_scalar(x_741)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_741;
}
lean_ctor_set(x_798, 0, x_792);
lean_ctor_set(x_798, 1, x_797);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_790);
lean_ctor_set(x_799, 1, x_798);
lean_ctor_set(x_28, 1, x_799);
lean_ctor_set(x_28, 0, x_759);
lean_ctor_set(x_27, 0, x_772);
lean_inc(x_2);
x_800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_800, 0, x_2);
lean_ctor_set(x_800, 1, x_27);
x_801 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_801, 0, x_800);
x_18 = x_801;
x_19 = x_789;
goto block_26;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_786);
lean_dec(x_782);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_744);
lean_dec(x_741);
lean_dec(x_739);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_802 = lean_ctor_get(x_787, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_787, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_804 = x_787;
} else {
 lean_dec_ref(x_787);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
else
{
lean_object* x_806; lean_object* x_807; 
x_806 = lean_array_fget(x_1, x_739);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_806);
x_807 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_806, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_nat_add(x_739, x_757);
lean_dec(x_739);
x_811 = lean_ctor_get(x_806, 0);
lean_inc(x_811);
lean_dec(x_806);
lean_inc(x_808);
lean_inc(x_811);
x_812 = l_Lean_mkAppB(x_773, x_811, x_808);
x_813 = lean_array_push(x_782, x_811);
x_814 = lean_array_push(x_813, x_808);
x_815 = l_Lean_Expr_bindingBody_x21(x_774);
lean_dec(x_774);
x_816 = l_Lean_Expr_bindingBody_x21(x_815);
lean_dec(x_815);
if (lean_is_scalar(x_744)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_744;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_816);
if (lean_is_scalar(x_741)) {
 x_818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_818 = x_741;
}
lean_ctor_set(x_818, 0, x_812);
lean_ctor_set(x_818, 1, x_817);
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_810);
lean_ctor_set(x_819, 1, x_818);
lean_ctor_set(x_28, 1, x_819);
lean_ctor_set(x_28, 0, x_759);
lean_ctor_set(x_27, 0, x_772);
lean_inc(x_2);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_2);
lean_ctor_set(x_820, 1, x_27);
x_821 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_821, 0, x_820);
x_18 = x_821;
x_19 = x_809;
goto block_26;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_806);
lean_dec(x_782);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_744);
lean_dec(x_741);
lean_dec(x_739);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_822 = lean_ctor_get(x_807, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_807, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_824 = x_807;
} else {
 lean_dec_ref(x_807);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(1, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_822);
lean_ctor_set(x_825, 1, x_823);
return x_825;
}
}
}
case 3:
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_770);
x_826 = lean_array_push(x_742, x_17);
if (lean_is_scalar(x_744)) {
 x_827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_827 = x_744;
}
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_774);
if (lean_is_scalar(x_741)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_741;
}
lean_ctor_set(x_828, 0, x_773);
lean_ctor_set(x_828, 1, x_827);
x_829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_829, 0, x_739);
lean_ctor_set(x_829, 1, x_828);
lean_ctor_set(x_28, 1, x_829);
lean_ctor_set(x_28, 0, x_759);
lean_ctor_set(x_27, 0, x_772);
lean_inc(x_2);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_2);
lean_ctor_set(x_830, 1, x_27);
x_831 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_831, 0, x_830);
x_18 = x_831;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_770);
lean_dec(x_744);
lean_dec(x_741);
lean_free_object(x_27);
lean_free_object(x_28);
lean_inc(x_17);
x_832 = lean_array_push(x_742, x_17);
x_833 = l_Lean_Expr_bindingDomain_x21(x_774);
x_834 = lean_expr_instantiate_rev(x_833, x_832);
lean_dec(x_833);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_835 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_834);
x_838 = l_Lean_Meta_isExprDefEq(x_836, x_834, x_10, x_11, x_12, x_13, x_837);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; uint8_t x_840; 
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_unbox(x_839);
lean_dec(x_839);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_17);
x_841 = lean_ctor_get(x_838, 1);
lean_inc(x_841);
lean_dec(x_838);
x_842 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_834);
x_843 = l_Lean_Meta_trySynthInstance(x_834, x_842, x_10, x_11, x_12, x_13, x_841);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
if (lean_obj_tag(x_844) == 1)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_834);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_ctor_get(x_844, 0);
lean_inc(x_846);
lean_dec(x_844);
lean_inc(x_2);
x_847 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_739, x_759, x_772, x_2, x_773, x_832, x_774, x_846, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_845);
lean_dec(x_774);
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
lean_dec(x_847);
x_18 = x_848;
x_19 = x_849;
goto block_26;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; 
lean_dec(x_844);
x_850 = lean_ctor_get(x_843, 1);
lean_inc(x_850);
lean_dec(x_843);
x_851 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_852 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_851, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_850);
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_unbox(x_853);
lean_dec(x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_834);
x_855 = lean_ctor_get(x_852, 1);
lean_inc(x_855);
lean_dec(x_852);
x_856 = lean_box(0);
x_857 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_842, x_832, x_774, x_773, x_739, x_759, x_772, x_856, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_855);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_18 = x_858;
x_19 = x_859;
goto block_26;
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_860 = lean_ctor_get(x_852, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_852)) {
 lean_ctor_release(x_852, 0);
 lean_ctor_release(x_852, 1);
 x_861 = x_852;
} else {
 lean_dec_ref(x_852);
 x_861 = lean_box(0);
}
x_862 = l_Lean_indentExpr(x_834);
x_863 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_861)) {
 x_864 = lean_alloc_ctor(7, 2, 0);
} else {
 x_864 = x_861;
 lean_ctor_set_tag(x_864, 7);
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_862);
x_865 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_866 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_866, 0, x_864);
lean_ctor_set(x_866, 1, x_865);
x_867 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_851, x_866, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_860);
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
x_870 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_842, x_832, x_774, x_773, x_739, x_759, x_772, x_868, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_869);
lean_dec(x_868);
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
x_18 = x_871;
x_19 = x_872;
goto block_26;
}
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_739);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_873 = lean_ctor_get(x_843, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_843, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_875 = x_843;
} else {
 lean_dec_ref(x_843);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_874);
return x_876;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_834);
x_877 = lean_ctor_get(x_838, 1);
lean_inc(x_877);
lean_dec(x_838);
lean_inc(x_2);
x_878 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_739, x_759, x_772, x_2, x_773, x_832, x_774, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_877);
lean_dec(x_774);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_18 = x_879;
x_19 = x_880;
goto block_26;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_739);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_881 = lean_ctor_get(x_838, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_838, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_883 = x_838;
} else {
 lean_dec_ref(x_838);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_834);
lean_dec(x_832);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_739);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_885 = lean_ctor_get(x_835, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_835, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 lean_ctor_release(x_835, 1);
 x_887 = x_835;
} else {
 lean_dec_ref(x_835);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_888 = x_887;
}
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_886);
return x_888;
}
}
default: 
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_775);
lean_dec(x_770);
lean_dec(x_17);
x_889 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_890 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_889, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
lean_dec(x_890);
if (lean_is_scalar(x_744)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_744;
}
lean_ctor_set(x_892, 0, x_742);
lean_ctor_set(x_892, 1, x_774);
if (lean_is_scalar(x_741)) {
 x_893 = lean_alloc_ctor(0, 2, 0);
} else {
 x_893 = x_741;
}
lean_ctor_set(x_893, 0, x_773);
lean_ctor_set(x_893, 1, x_892);
x_894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_894, 0, x_739);
lean_ctor_set(x_894, 1, x_893);
lean_ctor_set(x_28, 1, x_894);
lean_ctor_set(x_28, 0, x_759);
lean_ctor_set(x_27, 0, x_772);
lean_inc(x_2);
x_895 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_895, 0, x_2);
lean_ctor_set(x_895, 1, x_27);
x_896 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_896, 0, x_895);
x_18 = x_896;
x_19 = x_891;
goto block_26;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_772);
lean_dec(x_759);
lean_dec(x_744);
lean_dec(x_742);
lean_dec(x_741);
lean_dec(x_739);
lean_free_object(x_27);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_897 = lean_ctor_get(x_890, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_890, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_899 = x_890;
} else {
 lean_dec_ref(x_890);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
}
}
}
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; 
x_901 = lean_ctor_get(x_27, 0);
lean_inc(x_901);
lean_dec(x_27);
x_902 = lean_ctor_get(x_29, 0);
lean_inc(x_902);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_903 = x_29;
} else {
 lean_dec_ref(x_29);
 x_903 = lean_box(0);
}
x_904 = lean_ctor_get(x_30, 0);
lean_inc(x_904);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_905 = x_30;
} else {
 lean_dec_ref(x_30);
 x_905 = lean_box(0);
}
x_906 = lean_ctor_get(x_31, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_31, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_908 = x_31;
} else {
 lean_dec_ref(x_31);
 x_908 = lean_box(0);
}
x_909 = lean_ctor_get(x_33, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_33, 1);
lean_inc(x_910);
x_911 = lean_ctor_get(x_33, 2);
lean_inc(x_911);
x_912 = lean_nat_dec_lt(x_910, x_911);
if (x_912 == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_911);
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_17);
if (lean_is_scalar(x_908)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_908;
}
lean_ctor_set(x_913, 0, x_906);
lean_ctor_set(x_913, 1, x_907);
if (lean_is_scalar(x_905)) {
 x_914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_914 = x_905;
}
lean_ctor_set(x_914, 0, x_904);
lean_ctor_set(x_914, 1, x_913);
if (lean_is_scalar(x_903)) {
 x_915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_915 = x_903;
}
lean_ctor_set(x_915, 0, x_902);
lean_ctor_set(x_915, 1, x_914);
lean_ctor_set(x_28, 1, x_915);
x_916 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_916, 0, x_901);
lean_ctor_set(x_916, 1, x_28);
lean_inc(x_2);
x_917 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_917, 0, x_2);
lean_ctor_set(x_917, 1, x_916);
x_918 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_918, 0, x_917);
x_18 = x_918;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_919; lean_object* x_920; uint8_t x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; uint8_t x_928; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_919 = x_33;
} else {
 lean_dec_ref(x_33);
 x_919 = lean_box(0);
}
x_920 = lean_array_fget(x_909, x_910);
x_921 = lean_unbox(x_920);
lean_dec(x_920);
x_922 = lean_unsigned_to_nat(1u);
x_923 = lean_nat_add(x_910, x_922);
lean_dec(x_910);
if (lean_is_scalar(x_919)) {
 x_924 = lean_alloc_ctor(0, 3, 0);
} else {
 x_924 = x_919;
}
lean_ctor_set(x_924, 0, x_909);
lean_ctor_set(x_924, 1, x_923);
lean_ctor_set(x_924, 2, x_911);
x_925 = lean_ctor_get(x_901, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_901, 1);
lean_inc(x_926);
x_927 = lean_ctor_get(x_901, 2);
lean_inc(x_927);
x_928 = lean_nat_dec_lt(x_926, x_927);
if (x_928 == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_927);
lean_dec(x_926);
lean_dec(x_925);
lean_dec(x_17);
if (lean_is_scalar(x_908)) {
 x_929 = lean_alloc_ctor(0, 2, 0);
} else {
 x_929 = x_908;
}
lean_ctor_set(x_929, 0, x_906);
lean_ctor_set(x_929, 1, x_907);
if (lean_is_scalar(x_905)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_905;
}
lean_ctor_set(x_930, 0, x_904);
lean_ctor_set(x_930, 1, x_929);
if (lean_is_scalar(x_903)) {
 x_931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_931 = x_903;
}
lean_ctor_set(x_931, 0, x_902);
lean_ctor_set(x_931, 1, x_930);
lean_ctor_set(x_28, 1, x_931);
lean_ctor_set(x_28, 0, x_924);
x_932 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_932, 0, x_901);
lean_ctor_set(x_932, 1, x_28);
lean_inc(x_2);
x_933 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_933, 0, x_2);
lean_ctor_set(x_933, 1, x_932);
x_934 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_934, 0, x_933);
x_18 = x_934;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 lean_ctor_release(x_901, 2);
 x_935 = x_901;
} else {
 lean_dec_ref(x_901);
 x_935 = lean_box(0);
}
x_936 = lean_array_fget(x_925, x_926);
x_937 = lean_nat_add(x_926, x_922);
lean_dec(x_926);
if (lean_is_scalar(x_935)) {
 x_938 = lean_alloc_ctor(0, 3, 0);
} else {
 x_938 = x_935;
}
lean_ctor_set(x_938, 0, x_925);
lean_ctor_set(x_938, 1, x_937);
lean_ctor_set(x_938, 2, x_927);
lean_inc(x_17);
x_939 = l_Lean_Expr_app___override(x_904, x_17);
x_940 = l_Lean_Expr_bindingBody_x21(x_907);
lean_dec(x_907);
x_941 = lean_box(x_921);
switch (lean_obj_tag(x_941)) {
case 0:
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec(x_17);
x_942 = lean_array_push(x_906, x_936);
if (lean_is_scalar(x_908)) {
 x_943 = lean_alloc_ctor(0, 2, 0);
} else {
 x_943 = x_908;
}
lean_ctor_set(x_943, 0, x_942);
lean_ctor_set(x_943, 1, x_940);
if (lean_is_scalar(x_905)) {
 x_944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_944 = x_905;
}
lean_ctor_set(x_944, 0, x_939);
lean_ctor_set(x_944, 1, x_943);
if (lean_is_scalar(x_903)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_903;
}
lean_ctor_set(x_945, 0, x_902);
lean_ctor_set(x_945, 1, x_944);
lean_ctor_set(x_28, 1, x_945);
lean_ctor_set(x_28, 0, x_924);
x_946 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_946, 0, x_938);
lean_ctor_set(x_946, 1, x_28);
lean_inc(x_2);
x_947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_947, 0, x_2);
lean_ctor_set(x_947, 1, x_946);
x_948 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_948, 0, x_947);
x_18 = x_948;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_949; lean_object* x_950; uint8_t x_951; 
lean_dec(x_936);
lean_inc(x_17);
x_949 = lean_array_push(x_906, x_17);
x_950 = lean_array_get_size(x_1);
x_951 = lean_nat_dec_lt(x_902, x_950);
lean_dec(x_950);
if (x_951 == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_952 = l_Lean_Meta_Simp_instInhabitedResult;
x_953 = l_outOfBounds___rarg(x_952);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_953);
x_954 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_953, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
x_957 = lean_nat_add(x_902, x_922);
lean_dec(x_902);
x_958 = lean_ctor_get(x_953, 0);
lean_inc(x_958);
lean_dec(x_953);
lean_inc(x_955);
lean_inc(x_958);
x_959 = l_Lean_mkAppB(x_939, x_958, x_955);
x_960 = lean_array_push(x_949, x_958);
x_961 = lean_array_push(x_960, x_955);
x_962 = l_Lean_Expr_bindingBody_x21(x_940);
lean_dec(x_940);
x_963 = l_Lean_Expr_bindingBody_x21(x_962);
lean_dec(x_962);
if (lean_is_scalar(x_908)) {
 x_964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_964 = x_908;
}
lean_ctor_set(x_964, 0, x_961);
lean_ctor_set(x_964, 1, x_963);
if (lean_is_scalar(x_905)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_905;
}
lean_ctor_set(x_965, 0, x_959);
lean_ctor_set(x_965, 1, x_964);
if (lean_is_scalar(x_903)) {
 x_966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_966 = x_903;
}
lean_ctor_set(x_966, 0, x_957);
lean_ctor_set(x_966, 1, x_965);
lean_ctor_set(x_28, 1, x_966);
lean_ctor_set(x_28, 0, x_924);
x_967 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_967, 0, x_938);
lean_ctor_set(x_967, 1, x_28);
lean_inc(x_2);
x_968 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_968, 0, x_2);
lean_ctor_set(x_968, 1, x_967);
x_969 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_969, 0, x_968);
x_18 = x_969;
x_19 = x_956;
goto block_26;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_953);
lean_dec(x_949);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_908);
lean_dec(x_905);
lean_dec(x_903);
lean_dec(x_902);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_970 = lean_ctor_get(x_954, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_954, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_972 = x_954;
} else {
 lean_dec_ref(x_954);
 x_972 = lean_box(0);
}
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(1, 2, 0);
} else {
 x_973 = x_972;
}
lean_ctor_set(x_973, 0, x_970);
lean_ctor_set(x_973, 1, x_971);
return x_973;
}
}
else
{
lean_object* x_974; lean_object* x_975; 
x_974 = lean_array_fget(x_1, x_902);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_974);
x_975 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_974, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
lean_dec(x_975);
x_978 = lean_nat_add(x_902, x_922);
lean_dec(x_902);
x_979 = lean_ctor_get(x_974, 0);
lean_inc(x_979);
lean_dec(x_974);
lean_inc(x_976);
lean_inc(x_979);
x_980 = l_Lean_mkAppB(x_939, x_979, x_976);
x_981 = lean_array_push(x_949, x_979);
x_982 = lean_array_push(x_981, x_976);
x_983 = l_Lean_Expr_bindingBody_x21(x_940);
lean_dec(x_940);
x_984 = l_Lean_Expr_bindingBody_x21(x_983);
lean_dec(x_983);
if (lean_is_scalar(x_908)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_908;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_984);
if (lean_is_scalar(x_905)) {
 x_986 = lean_alloc_ctor(0, 2, 0);
} else {
 x_986 = x_905;
}
lean_ctor_set(x_986, 0, x_980);
lean_ctor_set(x_986, 1, x_985);
if (lean_is_scalar(x_903)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_903;
}
lean_ctor_set(x_987, 0, x_978);
lean_ctor_set(x_987, 1, x_986);
lean_ctor_set(x_28, 1, x_987);
lean_ctor_set(x_28, 0, x_924);
x_988 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_988, 0, x_938);
lean_ctor_set(x_988, 1, x_28);
lean_inc(x_2);
x_989 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_989, 0, x_2);
lean_ctor_set(x_989, 1, x_988);
x_990 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_990, 0, x_989);
x_18 = x_990;
x_19 = x_977;
goto block_26;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_974);
lean_dec(x_949);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_908);
lean_dec(x_905);
lean_dec(x_903);
lean_dec(x_902);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_991 = lean_ctor_get(x_975, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_975, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_993 = x_975;
} else {
 lean_dec_ref(x_975);
 x_993 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_994 = x_993;
}
lean_ctor_set(x_994, 0, x_991);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
}
}
case 3:
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_936);
x_995 = lean_array_push(x_906, x_17);
if (lean_is_scalar(x_908)) {
 x_996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_996 = x_908;
}
lean_ctor_set(x_996, 0, x_995);
lean_ctor_set(x_996, 1, x_940);
if (lean_is_scalar(x_905)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_905;
}
lean_ctor_set(x_997, 0, x_939);
lean_ctor_set(x_997, 1, x_996);
if (lean_is_scalar(x_903)) {
 x_998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_998 = x_903;
}
lean_ctor_set(x_998, 0, x_902);
lean_ctor_set(x_998, 1, x_997);
lean_ctor_set(x_28, 1, x_998);
lean_ctor_set(x_28, 0, x_924);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_938);
lean_ctor_set(x_999, 1, x_28);
lean_inc(x_2);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_2);
lean_ctor_set(x_1000, 1, x_999);
x_1001 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1001, 0, x_1000);
x_18 = x_1001;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_936);
lean_dec(x_908);
lean_dec(x_905);
lean_dec(x_903);
lean_free_object(x_28);
lean_inc(x_17);
x_1002 = lean_array_push(x_906, x_17);
x_1003 = l_Lean_Expr_bindingDomain_x21(x_940);
x_1004 = lean_expr_instantiate_rev(x_1003, x_1002);
lean_dec(x_1003);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_1005 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1005) == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
lean_dec(x_1005);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1004);
x_1008 = l_Lean_Meta_isExprDefEq(x_1006, x_1004, x_10, x_11, x_12, x_13, x_1007);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; uint8_t x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_unbox(x_1009);
lean_dec(x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_17);
x_1011 = lean_ctor_get(x_1008, 1);
lean_inc(x_1011);
lean_dec(x_1008);
x_1012 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1004);
x_1013 = l_Lean_Meta_trySynthInstance(x_1004, x_1012, x_10, x_11, x_12, x_13, x_1011);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
if (lean_obj_tag(x_1014) == 1)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_1004);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
lean_dec(x_1013);
x_1016 = lean_ctor_get(x_1014, 0);
lean_inc(x_1016);
lean_dec(x_1014);
lean_inc(x_2);
x_1017 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_902, x_924, x_938, x_2, x_939, x_1002, x_940, x_1016, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1015);
lean_dec(x_940);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_18 = x_1018;
x_19 = x_1019;
goto block_26;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; 
lean_dec(x_1014);
x_1020 = lean_ctor_get(x_1013, 1);
lean_inc(x_1020);
lean_dec(x_1013);
x_1021 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_1022 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1021, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1020);
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_unbox(x_1023);
lean_dec(x_1023);
if (x_1024 == 0)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_1004);
x_1025 = lean_ctor_get(x_1022, 1);
lean_inc(x_1025);
lean_dec(x_1022);
x_1026 = lean_box(0);
x_1027 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1012, x_1002, x_940, x_939, x_902, x_924, x_938, x_1026, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1025);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_18 = x_1028;
x_19 = x_1029;
goto block_26;
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1030 = lean_ctor_get(x_1022, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1031 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1031 = lean_box(0);
}
x_1032 = l_Lean_indentExpr(x_1004);
x_1033 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_1031)) {
 x_1034 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1034 = x_1031;
 lean_ctor_set_tag(x_1034, 7);
}
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1032);
x_1035 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_1036 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_1021, x_1036, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1030);
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1040 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1012, x_1002, x_940, x_939, x_902, x_924, x_938, x_1038, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1039);
lean_dec(x_1038);
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
x_18 = x_1041;
x_19 = x_1042;
goto block_26;
}
}
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_1004);
lean_dec(x_1002);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_902);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1043 = lean_ctor_get(x_1013, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1013, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 x_1045 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1045 = lean_box(0);
}
if (lean_is_scalar(x_1045)) {
 x_1046 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1046 = x_1045;
}
lean_ctor_set(x_1046, 0, x_1043);
lean_ctor_set(x_1046, 1, x_1044);
return x_1046;
}
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_1004);
x_1047 = lean_ctor_get(x_1008, 1);
lean_inc(x_1047);
lean_dec(x_1008);
lean_inc(x_2);
x_1048 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_902, x_924, x_938, x_2, x_939, x_1002, x_940, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1047);
lean_dec(x_940);
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc(x_1050);
lean_dec(x_1048);
x_18 = x_1049;
x_19 = x_1050;
goto block_26;
}
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1004);
lean_dec(x_1002);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_902);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1051 = lean_ctor_get(x_1008, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1008, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1053 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1051);
lean_ctor_set(x_1054, 1, x_1052);
return x_1054;
}
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_1004);
lean_dec(x_1002);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_902);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1055 = lean_ctor_get(x_1005, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1005, 1);
lean_inc(x_1056);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1057 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1057)) {
 x_1058 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1058 = x_1057;
}
lean_ctor_set(x_1058, 0, x_1055);
lean_ctor_set(x_1058, 1, x_1056);
return x_1058;
}
}
default: 
{
lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_941);
lean_dec(x_936);
lean_dec(x_17);
x_1059 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_1060 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_1059, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1061 = lean_ctor_get(x_1060, 1);
lean_inc(x_1061);
lean_dec(x_1060);
if (lean_is_scalar(x_908)) {
 x_1062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1062 = x_908;
}
lean_ctor_set(x_1062, 0, x_906);
lean_ctor_set(x_1062, 1, x_940);
if (lean_is_scalar(x_905)) {
 x_1063 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1063 = x_905;
}
lean_ctor_set(x_1063, 0, x_939);
lean_ctor_set(x_1063, 1, x_1062);
if (lean_is_scalar(x_903)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_903;
}
lean_ctor_set(x_1064, 0, x_902);
lean_ctor_set(x_1064, 1, x_1063);
lean_ctor_set(x_28, 1, x_1064);
lean_ctor_set(x_28, 0, x_924);
x_1065 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1065, 0, x_938);
lean_ctor_set(x_1065, 1, x_28);
lean_inc(x_2);
x_1066 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1066, 0, x_2);
lean_ctor_set(x_1066, 1, x_1065);
x_1067 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1067, 0, x_1066);
x_18 = x_1067;
x_19 = x_1061;
goto block_26;
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_924);
lean_dec(x_908);
lean_dec(x_906);
lean_dec(x_905);
lean_dec(x_903);
lean_dec(x_902);
lean_free_object(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1068 = lean_ctor_get(x_1060, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1060, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_1060)) {
 lean_ctor_release(x_1060, 0);
 lean_ctor_release(x_1060, 1);
 x_1070 = x_1060;
} else {
 lean_dec_ref(x_1060);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_1068);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
}
}
}
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; uint8_t x_1085; 
x_1072 = lean_ctor_get(x_28, 0);
lean_inc(x_1072);
lean_dec(x_28);
x_1073 = lean_ctor_get(x_27, 0);
lean_inc(x_1073);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_1074 = x_27;
} else {
 lean_dec_ref(x_27);
 x_1074 = lean_box(0);
}
x_1075 = lean_ctor_get(x_29, 0);
lean_inc(x_1075);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_1076 = x_29;
} else {
 lean_dec_ref(x_29);
 x_1076 = lean_box(0);
}
x_1077 = lean_ctor_get(x_30, 0);
lean_inc(x_1077);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_1078 = x_30;
} else {
 lean_dec_ref(x_30);
 x_1078 = lean_box(0);
}
x_1079 = lean_ctor_get(x_31, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_31, 1);
lean_inc(x_1080);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_1081 = x_31;
} else {
 lean_dec_ref(x_31);
 x_1081 = lean_box(0);
}
x_1082 = lean_ctor_get(x_1072, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1072, 1);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1072, 2);
lean_inc(x_1084);
x_1085 = lean_nat_dec_lt(x_1083, x_1084);
if (x_1085 == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1084);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_17);
if (lean_is_scalar(x_1081)) {
 x_1086 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1086 = x_1081;
}
lean_ctor_set(x_1086, 0, x_1079);
lean_ctor_set(x_1086, 1, x_1080);
if (lean_is_scalar(x_1078)) {
 x_1087 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1087 = x_1078;
}
lean_ctor_set(x_1087, 0, x_1077);
lean_ctor_set(x_1087, 1, x_1086);
if (lean_is_scalar(x_1076)) {
 x_1088 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1088 = x_1076;
}
lean_ctor_set(x_1088, 0, x_1075);
lean_ctor_set(x_1088, 1, x_1087);
x_1089 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1089, 0, x_1072);
lean_ctor_set(x_1089, 1, x_1088);
if (lean_is_scalar(x_1074)) {
 x_1090 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1090 = x_1074;
}
lean_ctor_set(x_1090, 0, x_1073);
lean_ctor_set(x_1090, 1, x_1089);
lean_inc(x_2);
x_1091 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1091, 0, x_2);
lean_ctor_set(x_1091, 1, x_1090);
x_1092 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1092, 0, x_1091);
x_18 = x_1092;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; 
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 lean_ctor_release(x_1072, 2);
 x_1093 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1093 = lean_box(0);
}
x_1094 = lean_array_fget(x_1082, x_1083);
x_1095 = lean_unbox(x_1094);
lean_dec(x_1094);
x_1096 = lean_unsigned_to_nat(1u);
x_1097 = lean_nat_add(x_1083, x_1096);
lean_dec(x_1083);
if (lean_is_scalar(x_1093)) {
 x_1098 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1098 = x_1093;
}
lean_ctor_set(x_1098, 0, x_1082);
lean_ctor_set(x_1098, 1, x_1097);
lean_ctor_set(x_1098, 2, x_1084);
x_1099 = lean_ctor_get(x_1073, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1073, 1);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1073, 2);
lean_inc(x_1101);
x_1102 = lean_nat_dec_lt(x_1100, x_1101);
if (x_1102 == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
lean_dec(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_17);
if (lean_is_scalar(x_1081)) {
 x_1103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1103 = x_1081;
}
lean_ctor_set(x_1103, 0, x_1079);
lean_ctor_set(x_1103, 1, x_1080);
if (lean_is_scalar(x_1078)) {
 x_1104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1104 = x_1078;
}
lean_ctor_set(x_1104, 0, x_1077);
lean_ctor_set(x_1104, 1, x_1103);
if (lean_is_scalar(x_1076)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1076;
}
lean_ctor_set(x_1105, 0, x_1075);
lean_ctor_set(x_1105, 1, x_1104);
x_1106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1106, 0, x_1098);
lean_ctor_set(x_1106, 1, x_1105);
if (lean_is_scalar(x_1074)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_1074;
}
lean_ctor_set(x_1107, 0, x_1073);
lean_ctor_set(x_1107, 1, x_1106);
lean_inc(x_2);
x_1108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1108, 0, x_2);
lean_ctor_set(x_1108, 1, x_1107);
x_1109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1109, 0, x_1108);
x_18 = x_1109;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
if (lean_is_exclusive(x_1073)) {
 lean_ctor_release(x_1073, 0);
 lean_ctor_release(x_1073, 1);
 lean_ctor_release(x_1073, 2);
 x_1110 = x_1073;
} else {
 lean_dec_ref(x_1073);
 x_1110 = lean_box(0);
}
x_1111 = lean_array_fget(x_1099, x_1100);
x_1112 = lean_nat_add(x_1100, x_1096);
lean_dec(x_1100);
if (lean_is_scalar(x_1110)) {
 x_1113 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1113 = x_1110;
}
lean_ctor_set(x_1113, 0, x_1099);
lean_ctor_set(x_1113, 1, x_1112);
lean_ctor_set(x_1113, 2, x_1101);
lean_inc(x_17);
x_1114 = l_Lean_Expr_app___override(x_1077, x_17);
x_1115 = l_Lean_Expr_bindingBody_x21(x_1080);
lean_dec(x_1080);
x_1116 = lean_box(x_1095);
switch (lean_obj_tag(x_1116)) {
case 0:
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_17);
x_1117 = lean_array_push(x_1079, x_1111);
if (lean_is_scalar(x_1081)) {
 x_1118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1118 = x_1081;
}
lean_ctor_set(x_1118, 0, x_1117);
lean_ctor_set(x_1118, 1, x_1115);
if (lean_is_scalar(x_1078)) {
 x_1119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1119 = x_1078;
}
lean_ctor_set(x_1119, 0, x_1114);
lean_ctor_set(x_1119, 1, x_1118);
if (lean_is_scalar(x_1076)) {
 x_1120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1120 = x_1076;
}
lean_ctor_set(x_1120, 0, x_1075);
lean_ctor_set(x_1120, 1, x_1119);
x_1121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1121, 0, x_1098);
lean_ctor_set(x_1121, 1, x_1120);
if (lean_is_scalar(x_1074)) {
 x_1122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1122 = x_1074;
}
lean_ctor_set(x_1122, 0, x_1113);
lean_ctor_set(x_1122, 1, x_1121);
lean_inc(x_2);
x_1123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1123, 0, x_2);
lean_ctor_set(x_1123, 1, x_1122);
x_1124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1124, 0, x_1123);
x_18 = x_1124;
x_19 = x_14;
goto block_26;
}
case 2:
{
lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; 
lean_dec(x_1111);
lean_inc(x_17);
x_1125 = lean_array_push(x_1079, x_17);
x_1126 = lean_array_get_size(x_1);
x_1127 = lean_nat_dec_lt(x_1075, x_1126);
lean_dec(x_1126);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = l_Lean_Meta_Simp_instInhabitedResult;
x_1129 = l_outOfBounds___rarg(x_1128);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1129);
x_1130 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_1129, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1130, 1);
lean_inc(x_1132);
lean_dec(x_1130);
x_1133 = lean_nat_add(x_1075, x_1096);
lean_dec(x_1075);
x_1134 = lean_ctor_get(x_1129, 0);
lean_inc(x_1134);
lean_dec(x_1129);
lean_inc(x_1131);
lean_inc(x_1134);
x_1135 = l_Lean_mkAppB(x_1114, x_1134, x_1131);
x_1136 = lean_array_push(x_1125, x_1134);
x_1137 = lean_array_push(x_1136, x_1131);
x_1138 = l_Lean_Expr_bindingBody_x21(x_1115);
lean_dec(x_1115);
x_1139 = l_Lean_Expr_bindingBody_x21(x_1138);
lean_dec(x_1138);
if (lean_is_scalar(x_1081)) {
 x_1140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1140 = x_1081;
}
lean_ctor_set(x_1140, 0, x_1137);
lean_ctor_set(x_1140, 1, x_1139);
if (lean_is_scalar(x_1078)) {
 x_1141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1141 = x_1078;
}
lean_ctor_set(x_1141, 0, x_1135);
lean_ctor_set(x_1141, 1, x_1140);
if (lean_is_scalar(x_1076)) {
 x_1142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1142 = x_1076;
}
lean_ctor_set(x_1142, 0, x_1133);
lean_ctor_set(x_1142, 1, x_1141);
x_1143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1143, 0, x_1098);
lean_ctor_set(x_1143, 1, x_1142);
if (lean_is_scalar(x_1074)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1074;
}
lean_ctor_set(x_1144, 0, x_1113);
lean_ctor_set(x_1144, 1, x_1143);
lean_inc(x_2);
x_1145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1145, 0, x_2);
lean_ctor_set(x_1145, 1, x_1144);
x_1146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1146, 0, x_1145);
x_18 = x_1146;
x_19 = x_1132;
goto block_26;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1129);
lean_dec(x_1125);
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1081);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1147 = lean_ctor_get(x_1130, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1130, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1130)) {
 lean_ctor_release(x_1130, 0);
 lean_ctor_release(x_1130, 1);
 x_1149 = x_1130;
} else {
 lean_dec_ref(x_1130);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
else
{
lean_object* x_1151; lean_object* x_1152; 
x_1151 = lean_array_fget(x_1, x_1075);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1151);
x_1152 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_1151, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_nat_add(x_1075, x_1096);
lean_dec(x_1075);
x_1156 = lean_ctor_get(x_1151, 0);
lean_inc(x_1156);
lean_dec(x_1151);
lean_inc(x_1153);
lean_inc(x_1156);
x_1157 = l_Lean_mkAppB(x_1114, x_1156, x_1153);
x_1158 = lean_array_push(x_1125, x_1156);
x_1159 = lean_array_push(x_1158, x_1153);
x_1160 = l_Lean_Expr_bindingBody_x21(x_1115);
lean_dec(x_1115);
x_1161 = l_Lean_Expr_bindingBody_x21(x_1160);
lean_dec(x_1160);
if (lean_is_scalar(x_1081)) {
 x_1162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1162 = x_1081;
}
lean_ctor_set(x_1162, 0, x_1159);
lean_ctor_set(x_1162, 1, x_1161);
if (lean_is_scalar(x_1078)) {
 x_1163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1163 = x_1078;
}
lean_ctor_set(x_1163, 0, x_1157);
lean_ctor_set(x_1163, 1, x_1162);
if (lean_is_scalar(x_1076)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1076;
}
lean_ctor_set(x_1164, 0, x_1155);
lean_ctor_set(x_1164, 1, x_1163);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_1098);
lean_ctor_set(x_1165, 1, x_1164);
if (lean_is_scalar(x_1074)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1074;
}
lean_ctor_set(x_1166, 0, x_1113);
lean_ctor_set(x_1166, 1, x_1165);
lean_inc(x_2);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_2);
lean_ctor_set(x_1167, 1, x_1166);
x_1168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1168, 0, x_1167);
x_18 = x_1168;
x_19 = x_1154;
goto block_26;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1151);
lean_dec(x_1125);
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1081);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1169 = lean_ctor_get(x_1152, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1152, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1152)) {
 lean_ctor_release(x_1152, 0);
 lean_ctor_release(x_1152, 1);
 x_1171 = x_1152;
} else {
 lean_dec_ref(x_1152);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1170);
return x_1172;
}
}
}
case 3:
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
lean_dec(x_1111);
x_1173 = lean_array_push(x_1079, x_17);
if (lean_is_scalar(x_1081)) {
 x_1174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1174 = x_1081;
}
lean_ctor_set(x_1174, 0, x_1173);
lean_ctor_set(x_1174, 1, x_1115);
if (lean_is_scalar(x_1078)) {
 x_1175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1175 = x_1078;
}
lean_ctor_set(x_1175, 0, x_1114);
lean_ctor_set(x_1175, 1, x_1174);
if (lean_is_scalar(x_1076)) {
 x_1176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1176 = x_1076;
}
lean_ctor_set(x_1176, 0, x_1075);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1177, 0, x_1098);
lean_ctor_set(x_1177, 1, x_1176);
if (lean_is_scalar(x_1074)) {
 x_1178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1178 = x_1074;
}
lean_ctor_set(x_1178, 0, x_1113);
lean_ctor_set(x_1178, 1, x_1177);
lean_inc(x_2);
x_1179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1179, 0, x_2);
lean_ctor_set(x_1179, 1, x_1178);
x_1180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1180, 0, x_1179);
x_18 = x_1180;
x_19 = x_14;
goto block_26;
}
case 5:
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
lean_dec(x_1111);
lean_dec(x_1081);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1074);
lean_inc(x_17);
x_1181 = lean_array_push(x_1079, x_17);
x_1182 = l_Lean_Expr_bindingDomain_x21(x_1115);
x_1183 = lean_expr_instantiate_rev(x_1182, x_1181);
lean_dec(x_1182);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_1184 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
x_1186 = lean_ctor_get(x_1184, 1);
lean_inc(x_1186);
lean_dec(x_1184);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1183);
x_1187 = l_Lean_Meta_isExprDefEq(x_1185, x_1183, x_10, x_11, x_12, x_13, x_1186);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; uint8_t x_1189; 
x_1188 = lean_ctor_get(x_1187, 0);
lean_inc(x_1188);
x_1189 = lean_unbox(x_1188);
lean_dec(x_1188);
if (x_1189 == 0)
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
lean_dec(x_17);
x_1190 = lean_ctor_get(x_1187, 1);
lean_inc(x_1190);
lean_dec(x_1187);
x_1191 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1183);
x_1192 = l_Lean_Meta_trySynthInstance(x_1183, x_1191, x_10, x_11, x_12, x_13, x_1190);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; 
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
if (lean_obj_tag(x_1193) == 1)
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_1183);
x_1194 = lean_ctor_get(x_1192, 1);
lean_inc(x_1194);
lean_dec(x_1192);
x_1195 = lean_ctor_get(x_1193, 0);
lean_inc(x_1195);
lean_dec(x_1193);
lean_inc(x_2);
x_1196 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1075, x_1098, x_1113, x_2, x_1114, x_1181, x_1115, x_1195, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1194);
lean_dec(x_1115);
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
lean_dec(x_1196);
x_18 = x_1197;
x_19 = x_1198;
goto block_26;
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; uint8_t x_1203; 
lean_dec(x_1193);
x_1199 = lean_ctor_get(x_1192, 1);
lean_inc(x_1199);
lean_dec(x_1192);
x_1200 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_1201 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1200, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1199);
x_1202 = lean_ctor_get(x_1201, 0);
lean_inc(x_1202);
x_1203 = lean_unbox(x_1202);
lean_dec(x_1202);
if (x_1203 == 0)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1183);
x_1204 = lean_ctor_get(x_1201, 1);
lean_inc(x_1204);
lean_dec(x_1201);
x_1205 = lean_box(0);
x_1206 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1191, x_1181, x_1115, x_1114, x_1075, x_1098, x_1113, x_1205, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1204);
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_18 = x_1207;
x_19 = x_1208;
goto block_26;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1209 = lean_ctor_get(x_1201, 1);
lean_inc(x_1209);
if (lean_is_exclusive(x_1201)) {
 lean_ctor_release(x_1201, 0);
 lean_ctor_release(x_1201, 1);
 x_1210 = x_1201;
} else {
 lean_dec_ref(x_1201);
 x_1210 = lean_box(0);
}
x_1211 = l_Lean_indentExpr(x_1183);
x_1212 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_1210)) {
 x_1213 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1213 = x_1210;
 lean_ctor_set_tag(x_1213, 7);
}
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1211);
x_1214 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_1215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1215, 0, x_1213);
lean_ctor_set(x_1215, 1, x_1214);
x_1216 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_1200, x_1215, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1209);
x_1217 = lean_ctor_get(x_1216, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1216, 1);
lean_inc(x_1218);
lean_dec(x_1216);
x_1219 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1191, x_1181, x_1115, x_1114, x_1075, x_1098, x_1113, x_1217, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1218);
lean_dec(x_1217);
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1219, 1);
lean_inc(x_1221);
lean_dec(x_1219);
x_18 = x_1220;
x_19 = x_1221;
goto block_26;
}
}
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
lean_dec(x_1183);
lean_dec(x_1181);
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1075);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1222 = lean_ctor_get(x_1192, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1192, 1);
lean_inc(x_1223);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 lean_ctor_release(x_1192, 1);
 x_1224 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1224 = lean_box(0);
}
if (lean_is_scalar(x_1224)) {
 x_1225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1225 = x_1224;
}
lean_ctor_set(x_1225, 0, x_1222);
lean_ctor_set(x_1225, 1, x_1223);
return x_1225;
}
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
lean_dec(x_1183);
x_1226 = lean_ctor_get(x_1187, 1);
lean_inc(x_1226);
lean_dec(x_1187);
lean_inc(x_2);
x_1227 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1075, x_1098, x_1113, x_2, x_1114, x_1181, x_1115, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_1226);
lean_dec(x_1115);
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1227, 1);
lean_inc(x_1229);
lean_dec(x_1227);
x_18 = x_1228;
x_19 = x_1229;
goto block_26;
}
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_1183);
lean_dec(x_1181);
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1075);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1230 = lean_ctor_get(x_1187, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1187, 1);
lean_inc(x_1231);
if (lean_is_exclusive(x_1187)) {
 lean_ctor_release(x_1187, 0);
 lean_ctor_release(x_1187, 1);
 x_1232 = x_1187;
} else {
 lean_dec_ref(x_1187);
 x_1232 = lean_box(0);
}
if (lean_is_scalar(x_1232)) {
 x_1233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1233 = x_1232;
}
lean_ctor_set(x_1233, 0, x_1230);
lean_ctor_set(x_1233, 1, x_1231);
return x_1233;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
lean_dec(x_1183);
lean_dec(x_1181);
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1075);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1234 = lean_ctor_get(x_1184, 0);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1184, 1);
lean_inc(x_1235);
if (lean_is_exclusive(x_1184)) {
 lean_ctor_release(x_1184, 0);
 lean_ctor_release(x_1184, 1);
 x_1236 = x_1184;
} else {
 lean_dec_ref(x_1184);
 x_1236 = lean_box(0);
}
if (lean_is_scalar(x_1236)) {
 x_1237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1237 = x_1236;
}
lean_ctor_set(x_1237, 0, x_1234);
lean_ctor_set(x_1237, 1, x_1235);
return x_1237;
}
}
default: 
{
lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1116);
lean_dec(x_1111);
lean_dec(x_17);
x_1238 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_1239 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_1238, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1240 = lean_ctor_get(x_1239, 1);
lean_inc(x_1240);
lean_dec(x_1239);
if (lean_is_scalar(x_1081)) {
 x_1241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1241 = x_1081;
}
lean_ctor_set(x_1241, 0, x_1079);
lean_ctor_set(x_1241, 1, x_1115);
if (lean_is_scalar(x_1078)) {
 x_1242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1242 = x_1078;
}
lean_ctor_set(x_1242, 0, x_1114);
lean_ctor_set(x_1242, 1, x_1241);
if (lean_is_scalar(x_1076)) {
 x_1243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1243 = x_1076;
}
lean_ctor_set(x_1243, 0, x_1075);
lean_ctor_set(x_1243, 1, x_1242);
x_1244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1244, 0, x_1098);
lean_ctor_set(x_1244, 1, x_1243);
if (lean_is_scalar(x_1074)) {
 x_1245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1245 = x_1074;
}
lean_ctor_set(x_1245, 0, x_1113);
lean_ctor_set(x_1245, 1, x_1244);
lean_inc(x_2);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_2);
lean_ctor_set(x_1246, 1, x_1245);
x_1247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1247, 0, x_1246);
x_18 = x_1247;
x_19 = x_1240;
goto block_26;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1115);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1098);
lean_dec(x_1081);
lean_dec(x_1079);
lean_dec(x_1078);
lean_dec(x_1076);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_1248 = lean_ctor_get(x_1239, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1239, 1);
lean_inc(x_1249);
if (lean_is_exclusive(x_1239)) {
 lean_ctor_release(x_1239, 0);
 lean_ctor_release(x_1239, 1);
 x_1250 = x_1239;
} else {
 lean_dec_ref(x_1239);
 x_1250 = lean_box(0);
}
if (lean_is_scalar(x_1250)) {
 x_1251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1251 = x_1250;
}
lean_ctor_set(x_1251, 0, x_1248);
lean_ctor_set(x_1251, 1, x_1249);
return x_1251;
}
}
}
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1;
x_3 = l_instInhabitedOfMonad___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(629u);
x_4 = lean_unsigned_to_nat(61u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_expr_instantiate_rev(x_1, x_2);
x_17 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_16, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_20 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2;
x_21 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5(x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
if (x_6 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(x_3, x_4, x_5, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_22, x_11, x_12, x_13, x_14, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(x_3, x_4, x_5, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_array_get_size(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_toSubarray___rarg(x_2, x_23, x_22);
x_25 = lean_box(0);
lean_inc(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_21);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(x_5, x_25, x_6, x_7, x_8, x_31, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(x_43, x_42, x_9, x_25, x_41, x_10, x_44, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_40);
lean_dec(x_42);
lean_dec(x_43);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_32, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
lean_ctor_set(x_32, 0, x_48);
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (x_9 == 0)
{
if (x_10 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_21 = l_Lean_mkAppN(x_11, x_2);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_2 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_2 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_array_get_size(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_21 = l_Lean_Meta_getFunInfoNArgs(x_2, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Lean_Meta_Simp_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
x_30 = lean_array_get_size(x_29);
x_31 = l_Array_toSubarray___rarg(x_29, x_13, x_30);
x_32 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
lean_inc(x_31);
lean_ctor_set(x_25, 1, x_32);
lean_ctor_set(x_25, 0, x_31);
x_33 = lean_array_size(x_19);
x_34 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_22, x_24, x_27, x_19, x_33, x_34, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_35, 0, x_49);
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_dec(x_35);
x_51 = lean_box(0);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
lean_dec(x_1);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_dec(x_35);
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_ctor_get(x_38, 0);
lean_inc(x_58);
lean_dec(x_38);
x_59 = lean_ctor_get(x_39, 0);
lean_inc(x_59);
lean_dec(x_39);
x_60 = lean_ctor_get(x_40, 0);
lean_inc(x_60);
lean_dec(x_40);
x_61 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_62 = lean_box(0);
x_63 = lean_unbox(x_60);
lean_dec(x_60);
x_64 = lean_unbox(x_59);
lean_dec(x_59);
x_65 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_3, x_58, x_61, x_31, x_57, x_19, x_33, x_34, x_63, x_64, x_2, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
lean_dec(x_19);
lean_dec(x_57);
lean_dec(x_3);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_35);
if (x_66 == 0)
{
return x_35;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_25, 0);
x_71 = lean_ctor_get(x_25, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_25);
x_72 = lean_ctor_get(x_3, 2);
lean_inc(x_72);
x_73 = lean_array_get_size(x_72);
x_74 = l_Array_toSubarray___rarg(x_72, x_13, x_73);
x_75 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
lean_inc(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_array_size(x_19);
x_78 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_22, x_24, x_70, x_19, x_77, x_78, x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_71);
lean_dec(x_70);
lean_dec(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
x_91 = 1;
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_88);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_dec(x_79);
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
lean_dec(x_83);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
lean_dec(x_84);
x_100 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_101 = lean_box(0);
x_102 = lean_unbox(x_99);
lean_dec(x_99);
x_103 = lean_unbox(x_98);
lean_dec(x_98);
x_104 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_3, x_97, x_100, x_74, x_96, x_19, x_77, x_78, x_102, x_103, x_2, x_101, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
lean_dec(x_19);
lean_dec(x_96);
lean_dec(x_3);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_107 = x_79;
} else {
 lean_dec_ref(x_79);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_21);
if (x_109 == 0)
{
return x_21;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_21, 0);
x_111 = lean_ctor_get(x_21, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_21);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_11 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_25);
x_27 = lean_nat_dec_eq(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_11);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(x_1, x_10, x_22, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_35);
x_37 = lean_nat_dec_eq(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
x_41 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(x_1, x_10, x_32, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_17, x_18, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_8);
lean_dec(x_8);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = lean_unbox(x_8);
lean_dec(x_8);
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_1, x_19, x_3, x_4, x_5, x_20, x_21, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = lean_unbox(x_10);
lean_dec(x_10);
x_24 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_21, x_22, x_23, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4___boxed(lean_object** _args) {
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
size_t x_21; size_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = lean_unbox(x_9);
lean_dec(x_9);
x_24 = lean_unbox(x_10);
lean_dec(x_10);
x_25 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 0, 5);
lean_ctor_set_uint8(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, 1, x_2);
lean_ctor_set_uint8(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, 3, x_3);
lean_ctor_set_uint8(x_7, 4, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_10 = 0;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 0, 5);
lean_ctor_set_uint8(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, 1, x_2);
lean_ctor_set_uint8(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, 3, x_8);
lean_ctor_set_uint8(x_12, 4, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_simpDtConfig;
return x_14;
}
else
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 0, 5);
lean_ctor_set_uint8(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, 1, x_2);
lean_ctor_set_uint8(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, 3, x_8);
lean_ctor_set_uint8(x_17, 4, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getDtConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_mkCongrFun(x_4, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = lean_box(0);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_array_size(x_2);
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_17, x_18, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lean_mkAppN(x_22, x_2);
lean_ctor_set(x_8, 0, x_21);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_mkAppN(x_28, x_2);
lean_ctor_set(x_8, 0, x_26);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
x_38 = lean_array_size(x_2);
x_39 = 0;
x_40 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_38, x_39, x_37, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_mkAppN(x_44, x_2);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Meta_Simp_Result_addExtraArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Meta_Simp_Result_addExtraArgs(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = l_Lean_Meta_Simp_Result_addExtraArgs(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set(x_33, 0, x_1);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_1, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
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
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_Meta_Simp_Result_addExtraArgs(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
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
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
default: 
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_1);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = l_Lean_TransformStep_toStep___closed__1;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_7);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = l_Lean_Meta_Simp_Result_addExtraArgs(x_59, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_ctor_set(x_55, 0, x_62);
lean_ctor_set(x_60, 0, x_1);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
lean_ctor_set(x_55, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_55);
lean_free_object(x_1);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_55, 0);
lean_inc(x_70);
lean_dec(x_55);
x_71 = l_Lean_Meta_Simp_Result_addExtraArgs(x_70, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_1, 0, x_75);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_1);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = l_Lean_TransformStep_toStep___closed__1;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_7);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Meta_Simp_Result_addExtraArgs(x_84, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_87);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_85);
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Step_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_mkAppN(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_mkAppN(x_6, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_mkAppN(x_10, x_2);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkAppN(x_12, x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
default: 
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_mkAppN(x_19, x_2);
lean_ctor_set(x_16, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_mkAppN(x_21, x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_Lean_mkAppN(x_26, x_2);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_expr_eqv(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_MVarId_replaceTargetEq(x_1, x_15, x_14, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_applySimpResultToTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedResult___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__1);
l_Lean_Meta_Simp_instInhabitedResult___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__2);
l_Lean_Meta_Simp_instInhabitedResult = _init_l_Lean_Meta_Simp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult);
l_Lean_Meta_Simp_instInhabitedContext___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__1);
l_Lean_Meta_Simp_instInhabitedContext___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__2);
l_Lean_Meta_Simp_instInhabitedContext___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__3);
l_Lean_Meta_Simp_instInhabitedContext___closed__4 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__4);
l_Lean_Meta_Simp_instInhabitedContext___closed__5 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__5);
l_Lean_Meta_Simp_instInhabitedContext___closed__6 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__6);
l_Lean_Meta_Simp_instInhabitedContext___closed__7 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__7);
l_Lean_Meta_Simp_instInhabitedContext___closed__8 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__8);
l_Lean_Meta_Simp_instInhabitedContext___closed__9 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__9);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1);
l_Lean_Meta_Simp_instInhabitedUsedSimps = _init_l_Lean_Meta_Simp_instInhabitedUsedSimps();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedUsedSimps);
l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1();
l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1);
l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1 = _init_l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1);
l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2 = _init_l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2);
l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1 = _init_l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1);
l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__1);
l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2();
l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3);
l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4 = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4);
l_Lean_Meta_Simp_instInhabitedDiagnostics = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics);
l_Lean_Meta_Simp_instInhabitedStats___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedStats___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStats___closed__1);
l_Lean_Meta_Simp_instInhabitedStats = _init_l_Lean_Meta_Simp_instInhabitedStats();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStats);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed();
l_Lean_Meta_Simp_instInhabitedStep___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep___closed__1);
l_Lean_Meta_Simp_instInhabitedStep = _init_l_Lean_Meta_Simp_instInhabitedStep();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep);
l_Lean_TransformStep_toStep___closed__1 = _init_l_Lean_TransformStep_toStep___closed__1();
lean_mark_persistent(l_Lean_TransformStep_toStep___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry = _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry);
l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocs = _init_l_Lean_Meta_Simp_instInhabitedSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs);
l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1);
l_Lean_Meta_Simp_instInhabitedMethods___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__1);
l_Lean_Meta_Simp_instInhabitedMethods___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__2);
l_Lean_Meta_Simp_instInhabitedMethods___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__3);
l_Lean_Meta_Simp_instInhabitedMethods___closed__4 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__4);
l_Lean_Meta_Simp_instInhabitedMethods = _init_l_Lean_Meta_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods);
l_Lean_Meta_Simp_withFreshCache___rarg___closed__1 = _init_l_Lean_Meta_Simp_withFreshCache___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_withFreshCache___rarg___closed__1);
l_Lean_Meta_Simp_recordSimpTheorem___closed__1 = _init_l_Lean_Meta_Simp_recordSimpTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_recordSimpTheorem___closed__1);
l_Lean_Meta_Simp_Result_mkCast___closed__1 = _init_l_Lean_Meta_Simp_Result_mkCast___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Result_mkCast___closed__1);
l_Lean_Meta_Simp_Result_mkCast___closed__2 = _init_l_Lean_Meta_Simp_Result_mkCast___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Result_mkCast___closed__2);
l_Lean_Meta_Simp_mkImpCongr___closed__1 = _init_l_Lean_Meta_Simp_mkImpCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkImpCongr___closed__1);
l_Lean_Meta_Simp_mkImpCongr___closed__2 = _init_l_Lean_Meta_Simp_mkImpCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkImpCongr___closed__2);
l_Lean_Meta_Simp_mkImpCongr___closed__3 = _init_l_Lean_Meta_Simp_mkImpCongr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_mkImpCongr___closed__3);
l_Lean_Meta_Simp_mkImpCongr___closed__4 = _init_l_Lean_Meta_Simp_mkImpCongr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_mkImpCongr___closed__4);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6);
l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7);
l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1 = _init_l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1);
l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1();
l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4);
l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5 = _init_l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5);
l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1 = _init_l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
