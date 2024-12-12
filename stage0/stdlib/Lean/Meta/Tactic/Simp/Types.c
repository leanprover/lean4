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
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__1___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_recordSimpTheorem___closed__1;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object*, uint8_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__13;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__2;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__4;
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object*);
static lean_object* l_Lean_Meta_Simp_withFreshCache___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___boxed(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__7;
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__4;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__9;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Result_mkCast___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_Meta_Simp_withPreservedCache___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Simp_UsedSimps_insert___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed;
static size_t l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__2;
static lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__1;
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__12;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___boxed(lean_object**);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__2;
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___boxed(lean_object**);
static size_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__2___closed__2;
static lean_object* l_Lean_Meta_Simp_instInhabitedStats___closed__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStats;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_Meta_Simp_instInhabitedContext___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Simp_UsedSimps_toArray___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13;
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__4;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___spec__5(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__11;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedStep___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2;
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
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_instInhabitedExtensionState___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4;
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object*);
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
static uint64_t l_Lean_Meta_Simp_instInhabitedContext___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
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
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_1);
lean_ctor_set_uint8(x_5, 6, x_1);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_1);
lean_ctor_set_uint8(x_5, 9, x_2);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_1);
lean_ctor_set_uint8(x_5, 13, x_1);
lean_ctor_set_uint8(x_5, 14, x_1);
lean_ctor_set_uint8(x_5, 15, x_4);
lean_ctor_set_uint8(x_5, 16, x_1);
lean_ctor_set_uint8(x_5, 17, x_1);
return x_5;
}
}
static uint64_t _init_l_Lean_Meta_Simp_instInhabitedContext___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__4() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__3;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static uint32_t _init_l_Lean_Meta_Simp_instInhabitedContext___closed__5() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__7;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__12() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__9;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__11;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__1;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__4;
x_4 = l_Lean_Meta_Simp_instInhabitedContext___closed__5;
x_5 = l_Lean_Meta_Simp_instInhabitedContext___closed__6;
x_6 = l_Lean_Meta_Simp_instInhabitedContext___closed__12;
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_1);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set_uint32(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*7 + 4, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__13;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 10);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_27 = lean_st_ref_get(x_3, x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5;
x_32 = l_Lean_Environment_contains(x_30, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 10, x_36);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = 0;
x_38 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_8);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_9);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 1, x_10);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 2, x_11);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 3, x_12);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 4, x_13);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 5, x_14);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 6, x_15);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 7, x_16);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 9, x_18);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 10, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 11, x_19);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 12, x_20);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 13, x_21);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 14, x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 15, x_23);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 17, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 18, x_26);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5;
x_43 = l_Lean_Environment_contains(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_44 = x_1;
} else {
 lean_dec_ref(x_1);
 x_44 = lean_box(0);
}
x_45 = 0;
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 19);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_7);
lean_ctor_set(x_46, 1, x_8);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_9);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 1, x_10);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 2, x_11);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 3, x_12);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 4, x_13);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 5, x_14);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 6, x_15);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 7, x_16);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 9, x_18);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 10, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 11, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 12, x_20);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 13, x_21);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 14, x_22);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 15, x_23);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_24);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 17, x_25);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 18, x_26);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_7 = 0;
x_8 = 1;
x_9 = 2;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_11, 0, x_7);
lean_ctor_set_uint8(x_11, 1, x_7);
lean_ctor_set_uint8(x_11, 2, x_7);
lean_ctor_set_uint8(x_11, 3, x_7);
lean_ctor_set_uint8(x_11, 4, x_7);
lean_ctor_set_uint8(x_11, 5, x_8);
lean_ctor_set_uint8(x_11, 6, x_8);
lean_ctor_set_uint8(x_11, 7, x_7);
lean_ctor_set_uint8(x_11, 8, x_8);
lean_ctor_set_uint8(x_11, 9, x_9);
lean_ctor_set_uint8(x_11, 10, x_7);
lean_ctor_set_uint8(x_11, 11, x_2);
lean_ctor_set_uint8(x_11, 12, x_8);
lean_ctor_set_uint8(x_11, 13, x_3);
lean_ctor_set_uint8(x_11, 14, x_4);
lean_ctor_set_uint8(x_11, 15, x_10);
lean_ctor_set_uint8(x_11, 16, x_5);
lean_ctor_set_uint8(x_11, 17, x_6);
x_12 = l_Lean_Meta_Config_toConfigWithKey(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_8 = 0;
x_9 = 1;
x_10 = 2;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_12, 0, x_8);
lean_ctor_set_uint8(x_12, 1, x_8);
lean_ctor_set_uint8(x_12, 2, x_8);
lean_ctor_set_uint8(x_12, 3, x_8);
lean_ctor_set_uint8(x_12, 4, x_8);
lean_ctor_set_uint8(x_12, 5, x_9);
lean_ctor_set_uint8(x_12, 6, x_9);
lean_ctor_set_uint8(x_12, 7, x_8);
lean_ctor_set_uint8(x_12, 8, x_9);
lean_ctor_set_uint8(x_12, 9, x_10);
lean_ctor_set_uint8(x_12, 10, x_8);
lean_ctor_set_uint8(x_12, 11, x_3);
lean_ctor_set_uint8(x_12, 12, x_9);
lean_ctor_set_uint8(x_12, 13, x_4);
lean_ctor_set_uint8(x_12, 14, x_5);
lean_ctor_set_uint8(x_12, 15, x_11);
lean_ctor_set_uint8(x_12, 16, x_6);
lean_ctor_set_uint8(x_12, 17, x_7);
x_13 = l_Lean_Meta_Config_toConfigWithKey(x_12);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_19 = 0;
x_20 = 1;
x_21 = 2;
x_22 = 2;
x_23 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_23, 0, x_19);
lean_ctor_set_uint8(x_23, 1, x_19);
lean_ctor_set_uint8(x_23, 2, x_19);
lean_ctor_set_uint8(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, 4, x_19);
lean_ctor_set_uint8(x_23, 5, x_20);
lean_ctor_set_uint8(x_23, 6, x_20);
lean_ctor_set_uint8(x_23, 7, x_19);
lean_ctor_set_uint8(x_23, 8, x_20);
lean_ctor_set_uint8(x_23, 9, x_21);
lean_ctor_set_uint8(x_23, 10, x_19);
lean_ctor_set_uint8(x_23, 11, x_14);
lean_ctor_set_uint8(x_23, 12, x_20);
lean_ctor_set_uint8(x_23, 13, x_15);
lean_ctor_set_uint8(x_23, 14, x_16);
lean_ctor_set_uint8(x_23, 15, x_22);
lean_ctor_set_uint8(x_23, 16, x_17);
lean_ctor_set_uint8(x_23, 17, x_18);
x_24 = l_Lean_Meta_Config_toConfigWithKey(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(x_1, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_11);
x_13 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_11);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = l_UInt32_ofNatTruncate(x_14);
x_16 = lean_box(0);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_2);
lean_ctor_set(x_20, 4, x_3);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set_uint32(x_20, sizeof(void*)*7, x_15);
lean_ctor_set_uint32(x_20, sizeof(void*)*7 + 4, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 8, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_21);
x_24 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_21);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = l_UInt32_ofNatTruncate(x_25);
x_27 = lean_box(0);
x_28 = 0;
x_29 = lean_unsigned_to_nat(0u);
x_30 = 0;
x_31 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_2);
lean_ctor_set(x_31, 4, x_3);
lean_ctor_set(x_31, 5, x_27);
lean_ctor_set(x_31, 6, x_29);
lean_ctor_set_uint32(x_31, sizeof(void*)*7, x_26);
lean_ctor_set_uint32(x_31, sizeof(void*)*7 + 4, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 8, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_12);
lean_ctor_set_uint32(x_14, sizeof(void*)*7, x_7);
lean_ctor_set_uint32(x_14, sizeof(void*)*7 + 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*7 + 8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_2);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_12);
lean_ctor_set_uint32(x_14, sizeof(void*)*7, x_8);
lean_ctor_set_uint32(x_14, sizeof(void*)*7 + 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*7 + 8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 6);
lean_dec(x_9);
x_10 = lean_local_ctx_num_indices(x_7);
lean_ctor_set(x_1, 6, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
x_19 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_21 = lean_local_ctx_num_indices(x_7);
x_22 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_21);
lean_ctor_set_uint32(x_22, sizeof(void*)*7, x_15);
lean_ctor_set_uint32(x_22, sizeof(void*)*7 + 4, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 8, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Context_setLctxInitIndices(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 11, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 5);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 6);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 7);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 8);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 9);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 10);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 12);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 13);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 15);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 16);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 17);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 18);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_3);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 1, x_9);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 2, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 3, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 5, x_13);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 6, x_14);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 7, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 9, x_17);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 10, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 11, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 12, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 13, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 14, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 15, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 17, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 18, x_25);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_32 = lean_ctor_get(x_1, 3);
x_33 = lean_ctor_get(x_1, 4);
x_34 = lean_ctor_get(x_1, 5);
x_35 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_36 = lean_ctor_get(x_1, 6);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_41 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 1);
x_42 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 2);
x_43 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 3);
x_44 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 4);
x_45 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 5);
x_46 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 6);
x_47 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 7);
x_48 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 8);
x_49 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 9);
x_50 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 10);
x_51 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 12);
x_52 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 13);
x_53 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 14);
x_54 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 15);
x_55 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 16);
x_56 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 17);
x_57 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 18);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_58 = x_28;
} else {
 lean_dec_ref(x_28);
 x_58 = lean_box(0);
}
x_59 = 1;
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 19);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_38);
lean_ctor_set(x_60, 1, x_39);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_40);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 1, x_41);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 2, x_42);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 3, x_43);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 4, x_44);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 5, x_45);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 6, x_46);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 7, x_47);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 8, x_48);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 9, x_49);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 10, x_50);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 11, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 12, x_51);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 13, x_52);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 14, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 15, x_54);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 16, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 17, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 18, x_57);
x_61 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_29);
lean_ctor_set(x_61, 2, x_30);
lean_ctor_set(x_61, 3, x_32);
lean_ctor_set(x_61, 4, x_33);
lean_ctor_set(x_61, 5, x_34);
lean_ctor_set(x_61, 6, x_36);
lean_ctor_set_uint32(x_61, sizeof(void*)*7, x_31);
lean_ctor_set_uint32(x_61, sizeof(void*)*7 + 4, x_35);
lean_ctor_set_uint8(x_61, sizeof(void*)*7 + 8, x_37);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 2);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 3);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 4);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 5);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 6);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 8);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 9);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 10);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 11);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 12);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 15);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 16);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 17);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 18);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_9);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 2, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 3, x_11);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 4, x_12);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 5, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 6, x_14);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 7, x_15);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 9, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 10, x_18);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 11, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 12, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 14, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 15, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 17, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 18, x_25);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_ctor_get(x_1, 4);
x_33 = lean_ctor_get(x_1, 5);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_35 = lean_ctor_get(x_1, 6);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_40 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 1);
x_41 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 2);
x_42 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 3);
x_43 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 4);
x_44 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 5);
x_45 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 6);
x_46 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 7);
x_47 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 8);
x_48 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 9);
x_49 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 10);
x_50 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 11);
x_51 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 12);
x_52 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 14);
x_53 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 15);
x_54 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 16);
x_55 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 17);
x_56 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 18);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_57 = x_27;
} else {
 lean_dec_ref(x_27);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 19);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_38);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 1, x_40);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 2, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 3, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 4, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 5, x_44);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 6, x_45);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 7, x_46);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 8, x_47);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 9, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 10, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 11, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 12, x_51);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 14, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 15, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 16, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 17, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 18, x_56);
x_59 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_28);
lean_ctor_set(x_59, 2, x_29);
lean_ctor_set(x_59, 3, x_31);
lean_ctor_set(x_59, 4, x_32);
lean_ctor_set(x_59, 5, x_33);
lean_ctor_set(x_59, 6, x_35);
lean_ctor_set_uint32(x_59, sizeof(void*)*7, x_30);
lean_ctor_set_uint32(x_59, sizeof(void*)*7 + 4, x_34);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 8, x_36);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 2);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 3);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 4);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 5);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 6);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 7);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 8);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 9);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 10);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 11);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 12);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 13);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 15);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 16);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 17);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 18);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 2, x_9);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 3, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 4, x_11);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 5, x_12);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 6, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 7, x_14);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 9, x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 10, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 11, x_18);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 12, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 13, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 14, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 15, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 17, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 18, x_25);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*7);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_ctor_get(x_1, 4);
x_33 = lean_ctor_get(x_1, 5);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*7 + 4);
x_35 = lean_ctor_get(x_1, 6);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_40 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 2);
x_41 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 3);
x_42 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 4);
x_43 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 5);
x_44 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 6);
x_45 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 7);
x_46 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 8);
x_47 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 9);
x_48 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 10);
x_49 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 11);
x_50 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 12);
x_51 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 13);
x_52 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 14);
x_53 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 15);
x_54 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 16);
x_55 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 17);
x_56 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 18);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_57 = x_27;
} else {
 lean_dec_ref(x_27);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 19);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_38);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 2, x_40);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 3, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 4, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 5, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 6, x_44);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 7, x_45);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 8, x_46);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 9, x_47);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 10, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 11, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 12, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 13, x_51);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 14, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 15, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 16, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 17, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 18, x_56);
x_59 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_28);
lean_ctor_set(x_59, 2, x_29);
lean_ctor_set(x_59, 3, x_31);
lean_ctor_set(x_59, 4, x_32);
lean_ctor_set(x_59, 5, x_33);
lean_ctor_set(x_59, 6, x_35);
lean_ctor_set_uint32(x_59, sizeof(void*)*7, x_30);
lean_ctor_set_uint32(x_59, sizeof(void*)*7 + 4, x_34);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 8, x_36);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_Simp_Context_setMemoize(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
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
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__11;
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
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_20 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
x_6 = x_21;
goto block_11;
}
else
{
if (x_17 == 0)
{
if (x_19 == 0)
{
uint8_t x_22; 
x_22 = 1;
x_6 = x_22;
goto block_11;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_6 = x_23;
goto block_11;
}
}
else
{
if (x_19 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_6 = x_24;
goto block_11;
}
else
{
uint8_t x_25; 
x_25 = 1;
x_6 = x_25;
goto block_11;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = 0;
x_6 = x_26;
goto block_11;
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_27; 
lean_dec(x_15);
x_27 = 0;
x_6 = x_27;
goto block_11;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Meta_Origin_key(x_5);
x_29 = l_Lean_Meta_Origin_key(x_15);
lean_dec(x_15);
x_30 = lean_name_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_6 = x_30;
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
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 1);
lean_dec(x_11);
x_16 = lean_name_eq(x_12, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
if (x_13 == 0)
{
if (x_15 == 0)
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
else
{
return x_15;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = 0;
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_21);
x_22 = 0;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Meta_Origin_key(x_3);
x_24 = l_Lean_Meta_Origin_key(x_21);
lean_dec(x_21);
x_25 = lean_name_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
return x_25;
}
}
}
case 1:
{
lean_object* x_26; size_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_usize_shift_right(x_2, x_5);
x_1 = x_26;
x_2 = x_27;
goto _start;
}
default: 
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__3(x_30, x_31, lean_box(0), x_32, x_3);
lean_dec(x_31);
lean_dec(x_30);
return x_33;
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
x_5 = l_Lean_Name_hash___override(x_4);
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
x_11 = l_Lean_Name_hash___override(x_10);
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
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 1);
lean_dec(x_30);
x_35 = lean_name_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
x_17 = x_36;
goto block_29;
}
else
{
if (x_32 == 0)
{
if (x_34 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_17 = x_37;
goto block_29;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_17 = x_38;
goto block_29;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_17 = x_39;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_17 = x_40;
goto block_29;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_30);
x_41 = 0;
x_17 = x_41;
goto block_29;
}
}
else
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_42; 
lean_dec(x_30);
x_42 = 0;
x_17 = x_42;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_Origin_key(x_3);
x_44 = l_Lean_Meta_Origin_key(x_30);
lean_dec(x_30);
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_17 = x_45;
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
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 1);
x_35 = lean_name_eq(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
x_22 = x_36;
goto block_30;
}
else
{
if (x_32 == 0)
{
if (x_34 == 0)
{
uint8_t x_37; 
x_37 = 1;
x_22 = x_37;
goto block_30;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_22 = x_38;
goto block_30;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_22 = x_39;
goto block_30;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_22 = x_40;
goto block_30;
}
}
}
}
else
{
uint8_t x_41; 
x_41 = 0;
x_22 = x_41;
goto block_30;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_42; 
x_42 = 0;
x_22 = x_42;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Meta_Origin_key(x_4);
x_44 = l_Lean_Meta_Origin_key(x_19);
x_45 = lean_name_eq(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_22 = x_45;
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
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_usize_shift_right(x_2, x_9);
x_49 = lean_usize_add(x_3, x_8);
x_50 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_47, x_48, x_49, x_4, x_5);
lean_ctor_set(x_16, 0, x_50);
x_51 = lean_array_fset(x_18, x_12, x_16);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_7;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
x_54 = lean_usize_shift_right(x_2, x_9);
x_55 = lean_usize_add(x_3, x_8);
x_56 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5(x_53, x_54, x_55, x_4, x_5);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_array_fset(x_18, x_12, x_57);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_7;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_5);
x_61 = lean_array_fset(x_18, x_12, x_60);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_7;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; size_t x_66; uint8_t x_67; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(x_1, x_64, x_4, x_5);
x_66 = 7;
x_67 = lean_usize_dec_le(x_66, x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_65);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_dec(x_65);
x_73 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
x_74 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(x_3, x_71, x_72, lean_box(0), x_64, x_73);
lean_dec(x_72);
lean_dec(x_71);
return x_74;
}
else
{
return x_65;
}
}
else
{
return x_65;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_1, 0);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_1);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__7(x_77, x_78, x_4, x_5);
x_80 = 7;
x_81 = lean_usize_dec_le(x_80, x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_79);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_dec_lt(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Simp_UsedSimps_insert___spec__5___closed__1;
x_88 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Simp_UsedSimps_insert___spec__6(x_3, x_85, x_86, lean_box(0), x_78, x_87);
lean_dec(x_86);
lean_dec(x_85);
return x_88;
}
else
{
return x_79;
}
}
else
{
return x_79;
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
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_Simp_UsedSimps_insert___spec__1(x_1, x_2);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___closed__1;
lean_inc(x_3);
x_9 = l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(x_1, x_2, x_8, x_3, x_4, lean_box(0), lean_box(0));
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_le(x_4, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_1, x_11, x_3, x_10, lean_box(0), lean_box(0));
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_10, x_14);
lean_dec(x_10);
x_2 = x_13;
x_3 = x_15;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
return x_11;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
x_9 = 0;
if (x_8 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; lean_object* x_13; 
lean_inc(x_6);
x_11 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_4, x_3, x_6, x_6, lean_box(0), lean_box(0));
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_array_size(x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(x_12, x_9, x_11);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; lean_object* x_16; 
x_14 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_4, x_3, x_7, x_6, lean_box(0), lean_box(0));
lean_dec(x_6);
lean_dec(x_4);
x_15 = lean_array_size(x_14);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(x_15, x_9, x_14);
return x_16;
}
}
else
{
size_t x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_array_size(x_3);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Meta_Simp_UsedSimps_toArray___spec__4(x_17, x_9, x_3);
return x_18;
}
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_Lean_Meta_Simp_UsedSimps_toArray___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
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
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__6;
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
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__6;
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
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint32_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get_uint32(x_3, sizeof(void*)*7 + 4);
x_12 = 1;
x_13 = lean_uint32_add(x_11, x_12);
lean_ctor_set_uint32(x_3, sizeof(void*)*7 + 4, x_13);
x_14 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; uint8_t x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get_uint32(x_3, sizeof(void*)*7);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get_uint32(x_3, sizeof(void*)*7 + 4);
x_23 = lean_ctor_get(x_3, 6);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_25 = 1;
x_26 = lean_uint32_add(x_22, x_25);
x_27 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_19);
lean_ctor_set(x_27, 4, x_20);
lean_ctor_set(x_27, 5, x_21);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set_uint32(x_27, sizeof(void*)*7, x_18);
lean_ctor_set_uint32(x_27, sizeof(void*)*7 + 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 8, x_24);
x_28 = lean_apply_8(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withIncDischargeDepth___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 3);
lean_dec(x_12);
lean_ctor_set(x_4, 3, x_1);
x_13 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get_uint32(x_4, sizeof(void*)*7);
x_18 = lean_ctor_get(x_4, 4);
x_19 = lean_ctor_get(x_4, 5);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*7 + 4);
x_21 = lean_ctor_get(x_4, 6);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_23 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_1);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*7, x_17);
lean_ctor_set_uint32(x_23, sizeof(void*)*7 + 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_22);
x_24 = lean_apply_8(x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withSimpTheorems___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*7 + 8, x_11);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get_uint32(x_3, sizeof(void*)*7);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = lean_ctor_get(x_3, 5);
x_20 = lean_ctor_get_uint32(x_3, sizeof(void*)*7 + 4);
x_21 = lean_ctor_get(x_3, 6);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*7, x_16);
lean_ctor_set_uint32(x_23, sizeof(void*)*7 + 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_22);
x_24 = lean_apply_8(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withInDSimp___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
lean_ctor_set(x_5, 0, x_11);
lean_ctor_set_uint64(x_5, sizeof(void*)*6, x_12);
x_15 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 3);
x_27 = lean_ctor_get(x_5, 4);
x_28 = lean_ctor_get(x_5, 5);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 8);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 9);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_31 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set_uint64(x_31, sizeof(void*)*6, x_12);
lean_ctor_set_uint8(x_31, sizeof(void*)*6 + 8, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*6 + 9, x_30);
x_32 = lean_apply_8(x_1, x_2, x_3, x_4, x_31, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withSimpIndexConfig___rarg), 9, 0);
return x_2;
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
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__6;
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
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__11;
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
x_12 = lean_ctor_get(x_4, 5);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_4, 5, x_13);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get_uint32(x_4, sizeof(void*)*7);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get_uint32(x_4, sizeof(void*)*7 + 4);
x_22 = lean_ctor_get(x_4, 6);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 7, 9);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set_uint32(x_25, sizeof(void*)*7, x_18);
lean_ctor_set_uint32(x_25, sizeof(void*)*7 + 4, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 8, x_23);
x_26 = lean_apply_8(x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
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
x_8 = lean_ctor_get(x_1, 3);
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
x_8 = lean_ctor_get(x_1, 4);
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
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 8);
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
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__9;
x_3 = l_Lean_Meta_Simp_instInhabitedContext___closed__11;
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
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_21 = lean_name_eq(x_17, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_6 = x_22;
goto block_12;
}
else
{
if (x_18 == 0)
{
if (x_20 == 0)
{
uint8_t x_23; 
x_23 = 1;
x_6 = x_23;
goto block_12;
}
else
{
uint8_t x_24; 
x_24 = 0;
x_6 = x_24;
goto block_12;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_25; 
x_25 = 0;
x_6 = x_25;
goto block_12;
}
else
{
uint8_t x_26; 
x_26 = 1;
x_6 = x_26;
goto block_12;
}
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
x_27 = 0;
x_6 = x_27;
goto block_12;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = 0;
x_6 = x_28;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Meta_Origin_key(x_5);
x_30 = l_Lean_Meta_Origin_key(x_16);
lean_dec(x_16);
x_31 = lean_name_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_6 = x_31;
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
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
lean_dec(x_12);
x_22 = lean_name_eq(x_18, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_14 = x_23;
goto block_17;
}
else
{
if (x_19 == 0)
{
if (x_21 == 0)
{
uint8_t x_24; 
x_24 = 1;
x_14 = x_24;
goto block_17;
}
else
{
uint8_t x_25; 
x_25 = 0;
x_14 = x_25;
goto block_17;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_26; 
x_26 = 0;
x_14 = x_26;
goto block_17;
}
else
{
uint8_t x_27; 
x_27 = 1;
x_14 = x_27;
goto block_17;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
x_28 = 0;
x_14 = x_28;
goto block_17;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_29; 
lean_dec(x_12);
x_29 = 0;
x_14 = x_29;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Meta_Origin_key(x_3);
x_31 = l_Lean_Meta_Origin_key(x_12);
lean_dec(x_12);
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_14 = x_32;
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
lean_object* x_33; size_t x_34; 
lean_dec(x_5);
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_usize_shift_right(x_2, x_6);
x_1 = x_33;
x_2 = x_34;
goto _start;
}
default: 
{
lean_object* x_36; 
lean_dec(x_5);
x_36 = lean_box(0);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__3(x_37, x_38, lean_box(0), x_39, x_3);
lean_dec(x_38);
lean_dec(x_37);
return x_40;
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
x_5 = l_Lean_Name_hash___override(x_4);
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
x_11 = l_Lean_Name_hash___override(x_10);
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
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Simp_recordTriedSimpTheorem___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
x_28 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_27, x_1, x_29);
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
x_41 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_27, x_1, x_40);
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
x_53 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(x_51, x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_51, x_1, x_54);
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
x_65 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_51, x_1, x_64);
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
x_81 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__1(x_78, x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_78, x_1, x_82);
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
x_94 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_78, x_1, x_93);
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
x_3 = lean_unsigned_to_nat(1773u);
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
x_144 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_134, x_134);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_6, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_6, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = l_outOfBounds___rarg(x_25);
x_27 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_28;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
x_30 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_26);
x_31 = lean_array_set(x_21, x_6, x_30);
x_32 = 1;
x_33 = lean_box(x_32);
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_31);
x_34 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_34;
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_array_fget(x_21, x_6);
x_37 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_38;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_22);
x_40 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_36);
x_41 = lean_array_set(x_21, x_6, x_40);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_8, 1, x_43);
lean_ctor_set(x_8, 0, x_41);
x_44 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_44;
x_7 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_array_get_size(x_46);
x_49 = lean_nat_dec_lt(x_6, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_instInhabitedExpr;
x_51 = l_outOfBounds___rarg(x_50);
x_52 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
x_54 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_54;
x_7 = lean_box(0);
x_8 = x_53;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_47);
x_56 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_51);
x_57 = lean_array_set(x_46, x_6, x_56);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_61;
x_7 = lean_box(0);
x_8 = x_60;
goto _start;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_array_fget(x_46, x_6);
x_64 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_47);
x_66 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_66;
x_7 = lean_box(0);
x_8 = x_65;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_47);
x_68 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_63);
x_69 = lean_array_set(x_46, x_6, x_68);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_73;
x_7 = lean_box(0);
x_8 = x_72;
goto _start;
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_5);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_8);
lean_ctor_set(x_75, 1, x_13);
return x_75;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_11);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_14);
x_19 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(x_15, x_7, x_14, x_11, x_14, x_7, lean_box(0), x_18, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_14);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_31 = l_Lean_mkAppN(x_30, x_29);
lean_dec(x_29);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_35 = l_Lean_mkAppN(x_34, x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = l_Lean_isTracingEnabledForCore(x_1, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; double x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_26 = 0;
x_27 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_28 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_float(x_28, sizeof(void*)*2, x_25);
lean_ctor_set_float(x_28, sizeof(void*)*2 + 8, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 16, x_26);
x_29 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_11);
x_31 = l_Lean_PersistentArray_push___rarg(x_24, x_15);
lean_ctor_set(x_17, 0, x_31);
x_32 = lean_st_ref_set(x_9, x_16, x_19);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint64_t x_39; lean_object* x_40; double x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_42 = 0;
x_43 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_44 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_float(x_44, sizeof(void*)*2, x_41);
lean_ctor_set_float(x_44, sizeof(void*)*2 + 8, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*2 + 16, x_42);
x_45 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_46 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_46);
lean_ctor_set(x_15, 0, x_11);
x_47 = l_Lean_PersistentArray_push___rarg(x_40, x_15);
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_39);
lean_ctor_set(x_16, 3, x_48);
x_49 = lean_st_ref_set(x_9, x_16, x_19);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; double x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
x_56 = lean_ctor_get(x_16, 2);
x_57 = lean_ctor_get(x_16, 4);
x_58 = lean_ctor_get(x_16, 5);
x_59 = lean_ctor_get(x_16, 6);
x_60 = lean_ctor_get(x_16, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_61 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_62 = lean_ctor_get(x_17, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_63 = x_17;
} else {
 lean_dec_ref(x_17);
 x_63 = lean_box(0);
}
x_64 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_65 = 0;
x_66 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_67 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_float(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_float(x_67, sizeof(void*)*2 + 8, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 16, x_65);
x_68 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_69 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_68);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_69);
lean_ctor_set(x_15, 0, x_11);
x_70 = l_Lean_PersistentArray_push___rarg(x_62, x_15);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 1, 8);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint64(x_71, sizeof(void*)*1, x_61);
x_72 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_55);
lean_ctor_set(x_72, 2, x_56);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_57);
lean_ctor_set(x_72, 5, x_58);
lean_ctor_set(x_72, 6, x_59);
lean_ctor_set(x_72, 7, x_60);
x_73 = lean_st_ref_set(x_9, x_72, x_19);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; lean_object* x_89; double x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_ctor_get(x_16, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_16, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_16, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_16, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_16, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_16, 7);
lean_inc(x_85);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 x_86 = x_16;
} else {
 lean_dec_ref(x_16);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_88 = lean_ctor_get(x_17, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_89 = x_17;
} else {
 lean_dec_ref(x_17);
 x_89 = lean_box(0);
}
x_90 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1;
x_91 = 0;
x_92 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_93 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_float(x_93, sizeof(void*)*2, x_90);
lean_ctor_set_float(x_93, sizeof(void*)*2 + 8, x_90);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 16, x_91);
x_94 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_95 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_13);
lean_ctor_set(x_95, 2, x_94);
lean_inc(x_11);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_11);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_PersistentArray_push___rarg(x_88, x_96);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 1, 8);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_uint64(x_98, sizeof(void*)*1, x_87);
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(0, 8, 0);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_79);
lean_ctor_set(x_99, 1, x_80);
lean_ctor_set(x_99, 2, x_81);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set(x_99, 4, x_82);
lean_ctor_set(x_99, 5, x_83);
lean_ctor_set(x_99, 6, x_84);
lean_ctor_set(x_99, 7, x_85);
x_100 = lean_st_ref_set(x_9, x_99, x_78);
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
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app [", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_19 = lean_array_uget(x_5, x_7);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1;
x_32 = lean_array_get_size(x_3);
x_33 = lean_nat_dec_lt(x_29, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_35 = lean_infer_type(x_34, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_38 = l_Lean_Meta_whnfD(x_36, x_12, x_13, x_14, x_15, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_isArrow(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_42 = lean_dsimp(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_45 = l_Lean_Meta_Simp_mkCongrFun(x_30, x_43, x_12, x_13, x_14, x_15, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_49 = lean_apply_11(x_31, x_29, x_46, x_48, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_20 = x_50;
x_21 = x_51;
goto block_28;
}
else
{
uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_64 = lean_simp(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_67 = l_Lean_Meta_Simp_mkCongr(x_30, x_65, x_12, x_13, x_14, x_15, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_71 = lean_apply_11(x_31, x_29, x_68, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_20 = x_72;
x_21 = x_73;
goto block_28;
}
else
{
uint8_t x_74; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_78 = !lean_is_exclusive(x_67);
if (x_78 == 0)
{
return x_67;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_67, 0);
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_67);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_82 = !lean_is_exclusive(x_64);
if (x_82 == 0)
{
return x_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_64, 0);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_64);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_86 = !lean_is_exclusive(x_38);
if (x_86 == 0)
{
return x_38;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_38, 0);
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_38);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_90 = !lean_is_exclusive(x_35);
if (x_90 == 0)
{
return x_35;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_35, 0);
x_92 = lean_ctor_get(x_35, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_35);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6;
x_95 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_94, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_32);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_100 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_19, x_31, x_29, x_3, x_2, x_30, x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_20 = x_101;
x_21 = x_102;
goto block_28;
}
else
{
uint8_t x_103; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_95);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_108 = lean_ctor_get(x_95, 1);
x_109 = lean_ctor_get(x_95, 0);
lean_dec(x_109);
lean_inc(x_29);
x_110 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_MessageData_ofFormat(x_111);
x_113 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
lean_ctor_set_tag(x_95, 7);
lean_ctor_set(x_95, 1, x_112);
lean_ctor_set(x_95, 0, x_113);
x_114 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_95);
lean_ctor_set(x_115, 1, x_114);
x_116 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_MessageData_ofFormat(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_inc(x_19);
x_122 = l_Lean_MessageData_ofExpr(x_19);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_fget(x_3, x_29);
x_127 = lean_ctor_get_uint8(x_126, sizeof(void*)*1 + 1);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_128 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_94, x_131, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_135 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_19, x_31, x_29, x_3, x_2, x_30, x_133, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_134);
lean_dec(x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_20 = x_136;
x_21 = x_137;
goto block_28;
}
else
{
uint8_t x_138; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_138 = !lean_is_exclusive(x_135);
if (x_138 == 0)
{
return x_135;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_135, 0);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_135);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_125);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_94, x_145, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_149 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_19, x_31, x_29, x_3, x_2, x_30, x_147, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_148);
lean_dec(x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_20 = x_150;
x_21 = x_151;
goto block_28;
}
else
{
uint8_t x_152; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_152 = !lean_is_exclusive(x_149);
if (x_152 == 0)
{
return x_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_149);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_156 = lean_ctor_get(x_95, 1);
lean_inc(x_156);
lean_dec(x_95);
lean_inc(x_29);
x_157 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_MessageData_ofFormat(x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_19);
x_170 = l_Lean_MessageData_ofExpr(x_19);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_array_fget(x_3, x_29);
x_175 = lean_ctor_get_uint8(x_174, sizeof(void*)*1 + 1);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_94, x_179, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_156);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_183 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_19, x_31, x_29, x_3, x_2, x_30, x_181, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_182);
lean_dec(x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_20 = x_184;
x_21 = x_185;
goto block_28;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_190 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_173);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_94, x_193, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_156);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_197 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_19, x_31, x_29, x_3, x_2, x_30, x_195, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_196);
lean_dec(x_195);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_20 = x_198;
x_21 = x_199;
goto block_28;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_202 = x_197;
} else {
 lean_dec_ref(x_197);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_7 = x_26;
x_8 = x_24;
x_16 = x_21;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_array_size(x_2);
x_25 = 0;
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_2, x_14, x_21, x_22, x_2, x_24, x_25, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
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
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_getFunInfoNArgs(x_44, x_45, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_1);
x_53 = lean_array_size(x_2);
x_54 = 0;
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_2, x_42, x_49, x_50, x_2, x_53, x_54, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_49);
lean_dec(x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_46, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_46, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_67 = x_46;
} else {
 lean_dec_ref(x_46);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_10);
return x_69;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(640u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed), 16, 1);
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
x_27 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_22, x_19, x_4, x_6, x_7, x_8, x_5, x_25, x_26, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_22, x_19, x_4, x_6, x_7, x_8, x_5, x_9, x_28, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
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
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_3, x_38, x_19, x_37, x_39, x_6, x_8, x_7, x_9, x_41, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_36);
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
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_3, x_38, x_19, x_37, x_39, x_6, x_8, x_43, x_9, x_44, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_36);
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
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_50, x_51, x_7, x_8, x_9, x_52, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
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
x_56 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_54, x_6, x_7, x_8, x_9, x_55, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
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
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4;
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
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_59, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_60);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_8, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_array_uget(x_6, x_8);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_27, 2);
lean_inc(x_46);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_17);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_27, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_27, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_27, 0);
lean_dec(x_52);
x_53 = lean_array_fget(x_44, x_45);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_45, x_55);
lean_dec(x_45);
lean_ctor_set(x_27, 1, x_56);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_58 = lean_box(0);
x_59 = lean_unbox(x_36);
lean_dec(x_36);
x_60 = lean_unbox(x_39);
lean_dec(x_39);
x_61 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_62 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_27, x_54, x_20, x_30, x_33, x_59, x_60, x_42, x_61, x_58, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
lean_ctor_set(x_62, 0, x_66);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = 1;
x_73 = lean_usize_add(x_8, x_72);
x_8 = x_73;
x_9 = x_71;
x_17 = x_70;
goto _start;
}
}
else
{
uint8_t x_75; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_75 = !lean_is_exclusive(x_62);
if (x_75 == 0)
{
return x_62;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_62);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_array_get_size(x_3);
x_80 = lean_nat_dec_lt(x_42, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_81 = lean_box(0);
x_82 = lean_unbox(x_36);
lean_dec(x_36);
x_83 = lean_unbox(x_39);
lean_dec(x_39);
x_84 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_85 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_27, x_54, x_20, x_30, x_33, x_82, x_83, x_42, x_84, x_81, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; 
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_dec(x_85);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_95 = 1;
x_96 = lean_usize_add(x_8, x_95);
x_8 = x_96;
x_9 = x_94;
x_17 = x_93;
goto _start;
}
}
else
{
uint8_t x_98; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_98 = !lean_is_exclusive(x_85);
if (x_98 == 0)
{
return x_85;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_85, 0);
x_100 = lean_ctor_get(x_85, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_85);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_fget(x_3, x_42);
x_103 = l_Lean_Meta_ParamInfo_isInstImplicit(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_104 = lean_box(0);
x_105 = lean_unbox(x_36);
lean_dec(x_36);
x_106 = lean_unbox(x_39);
lean_dec(x_39);
x_107 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_108 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_27, x_54, x_20, x_30, x_33, x_105, x_106, x_42, x_107, x_104, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set(x_108, 0, x_112);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; 
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
lean_dec(x_108);
x_117 = lean_ctor_get(x_109, 0);
lean_inc(x_117);
lean_dec(x_109);
x_118 = 1;
x_119 = lean_usize_add(x_8, x_118);
x_8 = x_119;
x_9 = x_117;
x_17 = x_116;
goto _start;
}
}
else
{
uint8_t x_121; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_121 = !lean_is_exclusive(x_108);
if (x_121 == 0)
{
return x_108;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_108, 0);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_108);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; 
x_125 = lean_array_push(x_33, x_20);
x_126 = lean_nat_add(x_42, x_55);
lean_dec(x_42);
lean_ctor_set(x_25, 0, x_126);
lean_ctor_set(x_22, 0, x_125);
x_127 = 1;
x_128 = lean_usize_add(x_8, x_127);
x_8 = x_128;
goto _start;
}
}
}
}
else
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_27);
x_130 = lean_array_fget(x_44, x_45);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_45, x_132);
lean_dec(x_45);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_44);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_46);
x_135 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_136 = lean_box(0);
x_137 = lean_unbox(x_36);
lean_dec(x_36);
x_138 = lean_unbox(x_39);
lean_dec(x_39);
x_139 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_140 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_134, x_131, x_20, x_30, x_33, x_137, x_138, x_42, x_139, x_136, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = lean_ctor_get(x_141, 0);
lean_inc(x_147);
lean_dec(x_141);
x_148 = 1;
x_149 = lean_usize_add(x_8, x_148);
x_8 = x_149;
x_9 = x_147;
x_17 = x_146;
goto _start;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_151 = lean_ctor_get(x_140, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_153 = x_140;
} else {
 lean_dec_ref(x_140);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_array_get_size(x_3);
x_156 = lean_nat_dec_lt(x_42, x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_157 = lean_box(0);
x_158 = lean_unbox(x_36);
lean_dec(x_36);
x_159 = lean_unbox(x_39);
lean_dec(x_39);
x_160 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_161 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_134, x_131, x_20, x_30, x_33, x_158, x_159, x_42, x_160, x_157, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_dec(x_162);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; 
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
lean_dec(x_162);
x_169 = 1;
x_170 = lean_usize_add(x_8, x_169);
x_8 = x_170;
x_9 = x_168;
x_17 = x_167;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_172 = lean_ctor_get(x_161, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_174 = x_161;
} else {
 lean_dec_ref(x_161);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_array_fget(x_3, x_42);
x_177 = l_Lean_Meta_ParamInfo_isInstImplicit(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; lean_object* x_182; 
lean_free_object(x_25);
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_178 = lean_box(0);
x_179 = lean_unbox(x_36);
lean_dec(x_36);
x_180 = lean_unbox(x_39);
lean_dec(x_39);
x_181 = lean_unbox(x_43);
lean_dec(x_43);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_182 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_134, x_131, x_20, x_30, x_33, x_179, x_180, x_42, x_181, x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; size_t x_190; size_t x_191; 
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
lean_dec(x_182);
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
lean_dec(x_183);
x_190 = 1;
x_191 = lean_usize_add(x_8, x_190);
x_8 = x_191;
x_9 = x_189;
x_17 = x_188;
goto _start;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_193 = lean_ctor_get(x_182, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_195 = x_182;
} else {
 lean_dec_ref(x_182);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; size_t x_199; size_t x_200; 
x_197 = lean_array_push(x_33, x_20);
x_198 = lean_nat_add(x_42, x_132);
lean_dec(x_42);
lean_ctor_set(x_25, 0, x_198);
lean_ctor_set(x_22, 0, x_197);
lean_ctor_set(x_9, 0, x_134);
x_199 = 1;
x_200 = lean_usize_add(x_8, x_199);
x_8 = x_200;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get(x_25, 0);
x_203 = lean_ctor_get(x_25, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_25);
x_204 = lean_ctor_get(x_27, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_27, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_27, 2);
lean_inc(x_206);
x_207 = lean_nat_dec_lt(x_205, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_203);
lean_ctor_set(x_24, 1, x_208);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_9);
lean_ctor_set(x_209, 1, x_17);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_210 = x_27;
} else {
 lean_dec_ref(x_27);
 x_210 = lean_box(0);
}
x_211 = lean_array_fget(x_204, x_205);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_205, x_213);
lean_dec(x_205);
if (lean_is_scalar(x_210)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_210;
}
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_206);
x_216 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_217 = lean_box(0);
x_218 = lean_unbox(x_36);
lean_dec(x_36);
x_219 = lean_unbox(x_39);
lean_dec(x_39);
x_220 = lean_unbox(x_203);
lean_dec(x_203);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_221 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_215, x_212, x_20, x_30, x_33, x_218, x_219, x_202, x_220, x_217, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec(x_222);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; size_t x_229; size_t x_230; 
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
lean_dec(x_221);
x_228 = lean_ctor_get(x_222, 0);
lean_inc(x_228);
lean_dec(x_222);
x_229 = 1;
x_230 = lean_usize_add(x_8, x_229);
x_8 = x_230;
x_9 = x_228;
x_17 = x_227;
goto _start;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_232 = lean_ctor_get(x_221, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_234 = x_221;
} else {
 lean_dec_ref(x_221);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_array_get_size(x_3);
x_237 = lean_nat_dec_lt(x_202, x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; lean_object* x_242; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_238 = lean_box(0);
x_239 = lean_unbox(x_36);
lean_dec(x_36);
x_240 = lean_unbox(x_39);
lean_dec(x_39);
x_241 = lean_unbox(x_203);
lean_dec(x_203);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_242 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_215, x_212, x_20, x_30, x_33, x_239, x_240, x_202, x_241, x_238, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
lean_dec(x_243);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; size_t x_250; size_t x_251; 
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
lean_dec(x_242);
x_249 = lean_ctor_get(x_243, 0);
lean_inc(x_249);
lean_dec(x_243);
x_250 = 1;
x_251 = lean_usize_add(x_8, x_250);
x_8 = x_251;
x_9 = x_249;
x_17 = x_248;
goto _start;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_253 = lean_ctor_get(x_242, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_242, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_255 = x_242;
} else {
 lean_dec_ref(x_242);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_array_fget(x_3, x_202);
x_258 = l_Lean_Meta_ParamInfo_isInstImplicit(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; lean_object* x_263; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_259 = lean_box(0);
x_260 = lean_unbox(x_36);
lean_dec(x_36);
x_261 = lean_unbox(x_39);
lean_dec(x_39);
x_262 = lean_unbox(x_203);
lean_dec(x_203);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_263 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_215, x_212, x_20, x_30, x_33, x_260, x_261, x_202, x_262, x_259, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_264, 0);
lean_inc(x_267);
lean_dec(x_264);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_265);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; size_t x_271; size_t x_272; 
x_269 = lean_ctor_get(x_263, 1);
lean_inc(x_269);
lean_dec(x_263);
x_270 = lean_ctor_get(x_264, 0);
lean_inc(x_270);
lean_dec(x_264);
x_271 = 1;
x_272 = lean_usize_add(x_8, x_271);
x_8 = x_272;
x_9 = x_270;
x_17 = x_269;
goto _start;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_274 = lean_ctor_get(x_263, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_263, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_276 = x_263;
} else {
 lean_dec_ref(x_263);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; size_t x_281; size_t x_282; 
x_278 = lean_array_push(x_33, x_20);
x_279 = lean_nat_add(x_202, x_213);
lean_dec(x_202);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_203);
lean_ctor_set(x_24, 1, x_280);
lean_ctor_set(x_22, 0, x_278);
lean_ctor_set(x_9, 0, x_215);
x_281 = 1;
x_282 = lean_usize_add(x_8, x_281);
x_8 = x_282;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_284 = lean_ctor_get(x_24, 0);
lean_inc(x_284);
lean_dec(x_24);
x_285 = lean_ctor_get(x_25, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_25, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_287 = x_25;
} else {
 lean_dec_ref(x_25);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_27, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_27, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_27, 2);
lean_inc(x_290);
x_291 = lean_nat_dec_lt(x_289, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_287)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_287;
}
lean_ctor_set(x_292, 0, x_285);
lean_ctor_set(x_292, 1, x_286);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_284);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_23, 1, x_293);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_9);
lean_ctor_set(x_294, 1, x_17);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_295 = x_27;
} else {
 lean_dec_ref(x_27);
 x_295 = lean_box(0);
}
x_296 = lean_array_fget(x_288, x_289);
x_297 = lean_unbox(x_296);
lean_dec(x_296);
x_298 = lean_unsigned_to_nat(1u);
x_299 = lean_nat_add(x_289, x_298);
lean_dec(x_289);
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_288);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_290);
x_301 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_301 == 0)
{
lean_object* x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; lean_object* x_306; 
lean_dec(x_287);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_302 = lean_box(0);
x_303 = lean_unbox(x_36);
lean_dec(x_36);
x_304 = lean_unbox(x_284);
lean_dec(x_284);
x_305 = lean_unbox(x_286);
lean_dec(x_286);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_306 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_300, x_297, x_20, x_30, x_33, x_303, x_304, x_285, x_305, x_302, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
lean_dec(x_307);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_309;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_308);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; size_t x_314; size_t x_315; 
x_312 = lean_ctor_get(x_306, 1);
lean_inc(x_312);
lean_dec(x_306);
x_313 = lean_ctor_get(x_307, 0);
lean_inc(x_313);
lean_dec(x_307);
x_314 = 1;
x_315 = lean_usize_add(x_8, x_314);
x_8 = x_315;
x_9 = x_313;
x_17 = x_312;
goto _start;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_317 = lean_ctor_get(x_306, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_306, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_319 = x_306;
} else {
 lean_dec_ref(x_306);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_array_get_size(x_3);
x_322 = lean_nat_dec_lt(x_285, x_321);
lean_dec(x_321);
if (x_322 == 0)
{
lean_object* x_323; uint8_t x_324; uint8_t x_325; uint8_t x_326; lean_object* x_327; 
lean_dec(x_287);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_323 = lean_box(0);
x_324 = lean_unbox(x_36);
lean_dec(x_36);
x_325 = lean_unbox(x_284);
lean_dec(x_284);
x_326 = lean_unbox(x_286);
lean_dec(x_286);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_327 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_300, x_297, x_20, x_30, x_33, x_324, x_325, x_285, x_326, x_323, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
x_331 = lean_ctor_get(x_328, 0);
lean_inc(x_331);
lean_dec(x_328);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_329);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; size_t x_335; size_t x_336; 
x_333 = lean_ctor_get(x_327, 1);
lean_inc(x_333);
lean_dec(x_327);
x_334 = lean_ctor_get(x_328, 0);
lean_inc(x_334);
lean_dec(x_328);
x_335 = 1;
x_336 = lean_usize_add(x_8, x_335);
x_8 = x_336;
x_9 = x_334;
x_17 = x_333;
goto _start;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_338 = lean_ctor_get(x_327, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_327, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_340 = x_327;
} else {
 lean_dec_ref(x_327);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
else
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_array_fget(x_3, x_285);
x_343 = l_Lean_Meta_ParamInfo_isInstImplicit(x_342);
lean_dec(x_342);
if (x_343 == 0)
{
lean_object* x_344; uint8_t x_345; uint8_t x_346; uint8_t x_347; lean_object* x_348; 
lean_dec(x_287);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_344 = lean_box(0);
x_345 = lean_unbox(x_36);
lean_dec(x_36);
x_346 = lean_unbox(x_284);
lean_dec(x_284);
x_347 = lean_unbox(x_286);
lean_dec(x_286);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_348 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_300, x_297, x_20, x_30, x_33, x_345, x_346, x_285, x_347, x_344, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
lean_dec(x_349);
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_350);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; size_t x_356; size_t x_357; 
x_354 = lean_ctor_get(x_348, 1);
lean_inc(x_354);
lean_dec(x_348);
x_355 = lean_ctor_get(x_349, 0);
lean_inc(x_355);
lean_dec(x_349);
x_356 = 1;
x_357 = lean_usize_add(x_8, x_356);
x_8 = x_357;
x_9 = x_355;
x_17 = x_354;
goto _start;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_359 = lean_ctor_get(x_348, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; size_t x_367; size_t x_368; 
x_363 = lean_array_push(x_33, x_20);
x_364 = lean_nat_add(x_285, x_298);
lean_dec(x_285);
if (lean_is_scalar(x_287)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_287;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_286);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_284);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_23, 1, x_366);
lean_ctor_set(x_22, 0, x_363);
lean_ctor_set(x_9, 0, x_300);
x_367 = 1;
x_368 = lean_usize_add(x_8, x_367);
x_8 = x_368;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_370 = lean_ctor_get(x_23, 0);
lean_inc(x_370);
lean_dec(x_23);
x_371 = lean_ctor_get(x_24, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_372 = x_24;
} else {
 lean_dec_ref(x_24);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_25, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_25, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_375 = x_25;
} else {
 lean_dec_ref(x_25);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_27, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_27, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_27, 2);
lean_inc(x_378);
x_379 = lean_nat_dec_lt(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_375)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_375;
}
lean_ctor_set(x_380, 0, x_373);
lean_ctor_set(x_380, 1, x_374);
if (lean_is_scalar(x_372)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_372;
}
lean_ctor_set(x_381, 0, x_371);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set(x_22, 1, x_382);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_9);
lean_ctor_set(x_383, 1, x_17);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_384 = x_27;
} else {
 lean_dec_ref(x_27);
 x_384 = lean_box(0);
}
x_385 = lean_array_fget(x_376, x_377);
x_386 = lean_unbox(x_385);
lean_dec(x_385);
x_387 = lean_unsigned_to_nat(1u);
x_388 = lean_nat_add(x_377, x_387);
lean_dec(x_377);
if (lean_is_scalar(x_384)) {
 x_389 = lean_alloc_ctor(0, 3, 0);
} else {
 x_389 = x_384;
}
lean_ctor_set(x_389, 0, x_376);
lean_ctor_set(x_389, 1, x_388);
lean_ctor_set(x_389, 2, x_378);
x_390 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; uint8_t x_393; uint8_t x_394; lean_object* x_395; 
lean_dec(x_375);
lean_dec(x_372);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_391 = lean_box(0);
x_392 = lean_unbox(x_370);
lean_dec(x_370);
x_393 = lean_unbox(x_371);
lean_dec(x_371);
x_394 = lean_unbox(x_374);
lean_dec(x_374);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_395 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_389, x_386, x_20, x_30, x_33, x_392, x_393, x_373, x_394, x_391, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_398 = x_395;
} else {
 lean_dec_ref(x_395);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_396, 0);
lean_inc(x_399);
lean_dec(x_396);
if (lean_is_scalar(x_398)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_398;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_397);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; size_t x_403; size_t x_404; 
x_401 = lean_ctor_get(x_395, 1);
lean_inc(x_401);
lean_dec(x_395);
x_402 = lean_ctor_get(x_396, 0);
lean_inc(x_402);
lean_dec(x_396);
x_403 = 1;
x_404 = lean_usize_add(x_8, x_403);
x_8 = x_404;
x_9 = x_402;
x_17 = x_401;
goto _start;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_406 = lean_ctor_get(x_395, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_395, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_408 = x_395;
} else {
 lean_dec_ref(x_395);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_array_get_size(x_3);
x_411 = lean_nat_dec_lt(x_373, x_410);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; uint8_t x_414; uint8_t x_415; lean_object* x_416; 
lean_dec(x_375);
lean_dec(x_372);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_412 = lean_box(0);
x_413 = lean_unbox(x_370);
lean_dec(x_370);
x_414 = lean_unbox(x_371);
lean_dec(x_371);
x_415 = lean_unbox(x_374);
lean_dec(x_374);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_416 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_389, x_386, x_20, x_30, x_33, x_413, x_414, x_373, x_415, x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = lean_ctor_get(x_417, 0);
lean_inc(x_420);
lean_dec(x_417);
if (lean_is_scalar(x_419)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_419;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; size_t x_424; size_t x_425; 
x_422 = lean_ctor_get(x_416, 1);
lean_inc(x_422);
lean_dec(x_416);
x_423 = lean_ctor_get(x_417, 0);
lean_inc(x_423);
lean_dec(x_417);
x_424 = 1;
x_425 = lean_usize_add(x_8, x_424);
x_8 = x_425;
x_9 = x_423;
x_17 = x_422;
goto _start;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_427 = lean_ctor_get(x_416, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_429 = x_416;
} else {
 lean_dec_ref(x_416);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
lean_object* x_431; uint8_t x_432; 
x_431 = lean_array_fget(x_3, x_373);
x_432 = l_Lean_Meta_ParamInfo_isInstImplicit(x_431);
lean_dec(x_431);
if (x_432 == 0)
{
lean_object* x_433; uint8_t x_434; uint8_t x_435; uint8_t x_436; lean_object* x_437; 
lean_dec(x_375);
lean_dec(x_372);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_9);
x_433 = lean_box(0);
x_434 = lean_unbox(x_370);
lean_dec(x_370);
x_435 = lean_unbox(x_371);
lean_dec(x_371);
x_436 = lean_unbox(x_374);
lean_dec(x_374);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_437 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_389, x_386, x_20, x_30, x_33, x_434, x_435, x_373, x_436, x_433, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_438, 0);
lean_inc(x_441);
lean_dec(x_438);
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_440;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_439);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; size_t x_445; size_t x_446; 
x_443 = lean_ctor_get(x_437, 1);
lean_inc(x_443);
lean_dec(x_437);
x_444 = lean_ctor_get(x_438, 0);
lean_inc(x_444);
lean_dec(x_438);
x_445 = 1;
x_446 = lean_usize_add(x_8, x_445);
x_8 = x_446;
x_9 = x_444;
x_17 = x_443;
goto _start;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_448 = lean_ctor_get(x_437, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_437, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_450 = x_437;
} else {
 lean_dec_ref(x_437);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; size_t x_457; size_t x_458; 
x_452 = lean_array_push(x_33, x_20);
x_453 = lean_nat_add(x_373, x_387);
lean_dec(x_373);
if (lean_is_scalar(x_375)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_375;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_374);
if (lean_is_scalar(x_372)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_372;
}
lean_ctor_set(x_455, 0, x_371);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_370);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_22, 1, x_456);
lean_ctor_set(x_22, 0, x_452);
lean_ctor_set(x_9, 0, x_389);
x_457 = 1;
x_458 = lean_usize_add(x_8, x_457);
x_8 = x_458;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_460 = lean_ctor_get(x_22, 0);
lean_inc(x_460);
lean_dec(x_22);
x_461 = lean_ctor_get(x_23, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_462 = x_23;
} else {
 lean_dec_ref(x_23);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_24, 0);
lean_inc(x_463);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_464 = x_24;
} else {
 lean_dec_ref(x_24);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_25, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_25, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_467 = x_25;
} else {
 lean_dec_ref(x_25);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_27, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_27, 1);
lean_inc(x_469);
x_470 = lean_ctor_get(x_27, 2);
lean_inc(x_470);
x_471 = lean_nat_dec_lt(x_469, x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_467)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_467;
}
lean_ctor_set(x_472, 0, x_465);
lean_ctor_set(x_472, 1, x_466);
if (lean_is_scalar(x_464)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_464;
}
lean_ctor_set(x_473, 0, x_463);
lean_ctor_set(x_473, 1, x_472);
if (lean_is_scalar(x_462)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_462;
}
lean_ctor_set(x_474, 0, x_461);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_460);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_21, 1, x_475);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_9);
lean_ctor_set(x_476, 1, x_17);
return x_476;
}
else
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_477 = x_27;
} else {
 lean_dec_ref(x_27);
 x_477 = lean_box(0);
}
x_478 = lean_array_fget(x_468, x_469);
x_479 = lean_unbox(x_478);
lean_dec(x_478);
x_480 = lean_unsigned_to_nat(1u);
x_481 = lean_nat_add(x_469, x_480);
lean_dec(x_469);
if (lean_is_scalar(x_477)) {
 x_482 = lean_alloc_ctor(0, 3, 0);
} else {
 x_482 = x_477;
}
lean_ctor_set(x_482, 0, x_468);
lean_ctor_set(x_482, 1, x_481);
lean_ctor_set(x_482, 2, x_470);
x_483 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_483 == 0)
{
lean_object* x_484; uint8_t x_485; uint8_t x_486; uint8_t x_487; lean_object* x_488; 
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_462);
lean_free_object(x_21);
lean_free_object(x_9);
x_484 = lean_box(0);
x_485 = lean_unbox(x_461);
lean_dec(x_461);
x_486 = lean_unbox(x_463);
lean_dec(x_463);
x_487 = lean_unbox(x_466);
lean_dec(x_466);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_488 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_482, x_479, x_20, x_30, x_460, x_485, x_486, x_465, x_487, x_484, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_489, 0);
lean_inc(x_492);
lean_dec(x_489);
if (lean_is_scalar(x_491)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_491;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_490);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; size_t x_496; size_t x_497; 
x_494 = lean_ctor_get(x_488, 1);
lean_inc(x_494);
lean_dec(x_488);
x_495 = lean_ctor_get(x_489, 0);
lean_inc(x_495);
lean_dec(x_489);
x_496 = 1;
x_497 = lean_usize_add(x_8, x_496);
x_8 = x_497;
x_9 = x_495;
x_17 = x_494;
goto _start;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_499 = lean_ctor_get(x_488, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_488, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_501 = x_488;
} else {
 lean_dec_ref(x_488);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
else
{
lean_object* x_503; uint8_t x_504; 
x_503 = lean_array_get_size(x_3);
x_504 = lean_nat_dec_lt(x_465, x_503);
lean_dec(x_503);
if (x_504 == 0)
{
lean_object* x_505; uint8_t x_506; uint8_t x_507; uint8_t x_508; lean_object* x_509; 
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_462);
lean_free_object(x_21);
lean_free_object(x_9);
x_505 = lean_box(0);
x_506 = lean_unbox(x_461);
lean_dec(x_461);
x_507 = lean_unbox(x_463);
lean_dec(x_463);
x_508 = lean_unbox(x_466);
lean_dec(x_466);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_509 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_482, x_479, x_20, x_30, x_460, x_506, x_507, x_465, x_508, x_505, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
x_513 = lean_ctor_get(x_510, 0);
lean_inc(x_513);
lean_dec(x_510);
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_511);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; size_t x_517; size_t x_518; 
x_515 = lean_ctor_get(x_509, 1);
lean_inc(x_515);
lean_dec(x_509);
x_516 = lean_ctor_get(x_510, 0);
lean_inc(x_516);
lean_dec(x_510);
x_517 = 1;
x_518 = lean_usize_add(x_8, x_517);
x_8 = x_518;
x_9 = x_516;
x_17 = x_515;
goto _start;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_520 = lean_ctor_get(x_509, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_509, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_522 = x_509;
} else {
 lean_dec_ref(x_509);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; uint8_t x_525; 
x_524 = lean_array_fget(x_3, x_465);
x_525 = l_Lean_Meta_ParamInfo_isInstImplicit(x_524);
lean_dec(x_524);
if (x_525 == 0)
{
lean_object* x_526; uint8_t x_527; uint8_t x_528; uint8_t x_529; lean_object* x_530; 
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_462);
lean_free_object(x_21);
lean_free_object(x_9);
x_526 = lean_box(0);
x_527 = lean_unbox(x_461);
lean_dec(x_461);
x_528 = lean_unbox(x_463);
lean_dec(x_463);
x_529 = lean_unbox(x_466);
lean_dec(x_466);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_530 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_482, x_479, x_20, x_30, x_460, x_527, x_528, x_465, x_529, x_526, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_533 = x_530;
} else {
 lean_dec_ref(x_530);
 x_533 = lean_box(0);
}
x_534 = lean_ctor_get(x_531, 0);
lean_inc(x_534);
lean_dec(x_531);
if (lean_is_scalar(x_533)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_533;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_532);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; size_t x_538; size_t x_539; 
x_536 = lean_ctor_get(x_530, 1);
lean_inc(x_536);
lean_dec(x_530);
x_537 = lean_ctor_get(x_531, 0);
lean_inc(x_537);
lean_dec(x_531);
x_538 = 1;
x_539 = lean_usize_add(x_8, x_538);
x_8 = x_539;
x_9 = x_537;
x_17 = x_536;
goto _start;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_541 = lean_ctor_get(x_530, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_530, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_543 = x_530;
} else {
 lean_dec_ref(x_530);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; size_t x_551; size_t x_552; 
x_545 = lean_array_push(x_460, x_20);
x_546 = lean_nat_add(x_465, x_480);
lean_dec(x_465);
if (lean_is_scalar(x_467)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_467;
}
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_466);
if (lean_is_scalar(x_464)) {
 x_548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_548 = x_464;
}
lean_ctor_set(x_548, 0, x_463);
lean_ctor_set(x_548, 1, x_547);
if (lean_is_scalar(x_462)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_462;
}
lean_ctor_set(x_549, 0, x_461);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_545);
lean_ctor_set(x_550, 1, x_549);
lean_ctor_set(x_21, 1, x_550);
lean_ctor_set(x_9, 0, x_482);
x_551 = 1;
x_552 = lean_usize_add(x_8, x_551);
x_8 = x_552;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; 
x_554 = lean_ctor_get(x_21, 0);
lean_inc(x_554);
lean_dec(x_21);
x_555 = lean_ctor_get(x_22, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_556 = x_22;
} else {
 lean_dec_ref(x_22);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_23, 0);
lean_inc(x_557);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_558 = x_23;
} else {
 lean_dec_ref(x_23);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_24, 0);
lean_inc(x_559);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_560 = x_24;
} else {
 lean_dec_ref(x_24);
 x_560 = lean_box(0);
}
x_561 = lean_ctor_get(x_25, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_25, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_563 = x_25;
} else {
 lean_dec_ref(x_25);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_27, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_27, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_27, 2);
lean_inc(x_566);
x_567 = lean_nat_dec_lt(x_565, x_566);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_563)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_563;
}
lean_ctor_set(x_568, 0, x_561);
lean_ctor_set(x_568, 1, x_562);
if (lean_is_scalar(x_560)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_560;
}
lean_ctor_set(x_569, 0, x_559);
lean_ctor_set(x_569, 1, x_568);
if (lean_is_scalar(x_558)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_558;
}
lean_ctor_set(x_570, 0, x_557);
lean_ctor_set(x_570, 1, x_569);
if (lean_is_scalar(x_556)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_556;
}
lean_ctor_set(x_571, 0, x_555);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_554);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_9, 1, x_572);
x_573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_573, 0, x_9);
lean_ctor_set(x_573, 1, x_17);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_574 = x_27;
} else {
 lean_dec_ref(x_27);
 x_574 = lean_box(0);
}
x_575 = lean_array_fget(x_564, x_565);
x_576 = lean_unbox(x_575);
lean_dec(x_575);
x_577 = lean_unsigned_to_nat(1u);
x_578 = lean_nat_add(x_565, x_577);
lean_dec(x_565);
if (lean_is_scalar(x_574)) {
 x_579 = lean_alloc_ctor(0, 3, 0);
} else {
 x_579 = x_574;
}
lean_ctor_set(x_579, 0, x_564);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set(x_579, 2, x_566);
x_580 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_580 == 0)
{
lean_object* x_581; uint8_t x_582; uint8_t x_583; uint8_t x_584; lean_object* x_585; 
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_556);
lean_free_object(x_9);
x_581 = lean_box(0);
x_582 = lean_unbox(x_557);
lean_dec(x_557);
x_583 = lean_unbox(x_559);
lean_dec(x_559);
x_584 = lean_unbox(x_562);
lean_dec(x_562);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_585 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_579, x_576, x_20, x_554, x_555, x_582, x_583, x_561, x_584, x_581, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
x_589 = lean_ctor_get(x_586, 0);
lean_inc(x_589);
lean_dec(x_586);
if (lean_is_scalar(x_588)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_588;
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_587);
return x_590;
}
else
{
lean_object* x_591; lean_object* x_592; size_t x_593; size_t x_594; 
x_591 = lean_ctor_get(x_585, 1);
lean_inc(x_591);
lean_dec(x_585);
x_592 = lean_ctor_get(x_586, 0);
lean_inc(x_592);
lean_dec(x_586);
x_593 = 1;
x_594 = lean_usize_add(x_8, x_593);
x_8 = x_594;
x_9 = x_592;
x_17 = x_591;
goto _start;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_596 = lean_ctor_get(x_585, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_585, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_598 = x_585;
} else {
 lean_dec_ref(x_585);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
}
else
{
lean_object* x_600; uint8_t x_601; 
x_600 = lean_array_get_size(x_3);
x_601 = lean_nat_dec_lt(x_561, x_600);
lean_dec(x_600);
if (x_601 == 0)
{
lean_object* x_602; uint8_t x_603; uint8_t x_604; uint8_t x_605; lean_object* x_606; 
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_556);
lean_free_object(x_9);
x_602 = lean_box(0);
x_603 = lean_unbox(x_557);
lean_dec(x_557);
x_604 = lean_unbox(x_559);
lean_dec(x_559);
x_605 = lean_unbox(x_562);
lean_dec(x_562);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_606 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_579, x_576, x_20, x_554, x_555, x_603, x_604, x_561, x_605, x_602, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_609 = x_606;
} else {
 lean_dec_ref(x_606);
 x_609 = lean_box(0);
}
x_610 = lean_ctor_get(x_607, 0);
lean_inc(x_610);
lean_dec(x_607);
if (lean_is_scalar(x_609)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_609;
}
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_608);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; size_t x_614; size_t x_615; 
x_612 = lean_ctor_get(x_606, 1);
lean_inc(x_612);
lean_dec(x_606);
x_613 = lean_ctor_get(x_607, 0);
lean_inc(x_613);
lean_dec(x_607);
x_614 = 1;
x_615 = lean_usize_add(x_8, x_614);
x_8 = x_615;
x_9 = x_613;
x_17 = x_612;
goto _start;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_617 = lean_ctor_get(x_606, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_606, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_619 = x_606;
} else {
 lean_dec_ref(x_606);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_object* x_621; uint8_t x_622; 
x_621 = lean_array_fget(x_3, x_561);
x_622 = l_Lean_Meta_ParamInfo_isInstImplicit(x_621);
lean_dec(x_621);
if (x_622 == 0)
{
lean_object* x_623; uint8_t x_624; uint8_t x_625; uint8_t x_626; lean_object* x_627; 
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_558);
lean_dec(x_556);
lean_free_object(x_9);
x_623 = lean_box(0);
x_624 = lean_unbox(x_557);
lean_dec(x_557);
x_625 = lean_unbox(x_559);
lean_dec(x_559);
x_626 = lean_unbox(x_562);
lean_dec(x_562);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_627 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_579, x_576, x_20, x_554, x_555, x_624, x_625, x_561, x_626, x_623, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_630 = x_627;
} else {
 lean_dec_ref(x_627);
 x_630 = lean_box(0);
}
x_631 = lean_ctor_get(x_628, 0);
lean_inc(x_631);
lean_dec(x_628);
if (lean_is_scalar(x_630)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_630;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_629);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; size_t x_635; size_t x_636; 
x_633 = lean_ctor_get(x_627, 1);
lean_inc(x_633);
lean_dec(x_627);
x_634 = lean_ctor_get(x_628, 0);
lean_inc(x_634);
lean_dec(x_628);
x_635 = 1;
x_636 = lean_usize_add(x_8, x_635);
x_8 = x_636;
x_9 = x_634;
x_17 = x_633;
goto _start;
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_638 = lean_ctor_get(x_627, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_627, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_640 = x_627;
} else {
 lean_dec_ref(x_627);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; size_t x_649; size_t x_650; 
x_642 = lean_array_push(x_555, x_20);
x_643 = lean_nat_add(x_561, x_577);
lean_dec(x_561);
if (lean_is_scalar(x_563)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_563;
}
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_562);
if (lean_is_scalar(x_560)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_560;
}
lean_ctor_set(x_645, 0, x_559);
lean_ctor_set(x_645, 1, x_644);
if (lean_is_scalar(x_558)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_558;
}
lean_ctor_set(x_646, 0, x_557);
lean_ctor_set(x_646, 1, x_645);
if (lean_is_scalar(x_556)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_556;
}
lean_ctor_set(x_647, 0, x_642);
lean_ctor_set(x_647, 1, x_646);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_554);
lean_ctor_set(x_648, 1, x_647);
lean_ctor_set(x_9, 1, x_648);
lean_ctor_set(x_9, 0, x_579);
x_649 = 1;
x_650 = lean_usize_add(x_8, x_649);
x_8 = x_650;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_652 = lean_ctor_get(x_9, 0);
lean_inc(x_652);
lean_dec(x_9);
x_653 = lean_ctor_get(x_21, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_654 = x_21;
} else {
 lean_dec_ref(x_21);
 x_654 = lean_box(0);
}
x_655 = lean_ctor_get(x_22, 0);
lean_inc(x_655);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_656 = x_22;
} else {
 lean_dec_ref(x_22);
 x_656 = lean_box(0);
}
x_657 = lean_ctor_get(x_23, 0);
lean_inc(x_657);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_658 = x_23;
} else {
 lean_dec_ref(x_23);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_24, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_660 = x_24;
} else {
 lean_dec_ref(x_24);
 x_660 = lean_box(0);
}
x_661 = lean_ctor_get(x_25, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_25, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_663 = x_25;
} else {
 lean_dec_ref(x_25);
 x_663 = lean_box(0);
}
x_664 = lean_ctor_get(x_652, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_652, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_652, 2);
lean_inc(x_666);
x_667 = lean_nat_dec_lt(x_665, x_666);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_663)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_663;
}
lean_ctor_set(x_668, 0, x_661);
lean_ctor_set(x_668, 1, x_662);
if (lean_is_scalar(x_660)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_660;
}
lean_ctor_set(x_669, 0, x_659);
lean_ctor_set(x_669, 1, x_668);
if (lean_is_scalar(x_658)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_658;
}
lean_ctor_set(x_670, 0, x_657);
lean_ctor_set(x_670, 1, x_669);
if (lean_is_scalar(x_656)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_656;
}
lean_ctor_set(x_671, 0, x_655);
lean_ctor_set(x_671, 1, x_670);
if (lean_is_scalar(x_654)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_654;
}
lean_ctor_set(x_672, 0, x_653);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_673, 0, x_652);
lean_ctor_set(x_673, 1, x_672);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_17);
return x_674;
}
else
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; 
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 lean_ctor_release(x_652, 2);
 x_675 = x_652;
} else {
 lean_dec_ref(x_652);
 x_675 = lean_box(0);
}
x_676 = lean_array_fget(x_664, x_665);
x_677 = lean_unbox(x_676);
lean_dec(x_676);
x_678 = lean_unsigned_to_nat(1u);
x_679 = lean_nat_add(x_665, x_678);
lean_dec(x_665);
if (lean_is_scalar(x_675)) {
 x_680 = lean_alloc_ctor(0, 3, 0);
} else {
 x_680 = x_675;
}
lean_ctor_set(x_680, 0, x_664);
lean_ctor_set(x_680, 1, x_679);
lean_ctor_set(x_680, 2, x_666);
x_681 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 14);
if (x_681 == 0)
{
lean_object* x_682; uint8_t x_683; uint8_t x_684; uint8_t x_685; lean_object* x_686; 
lean_dec(x_663);
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
x_682 = lean_box(0);
x_683 = lean_unbox(x_657);
lean_dec(x_657);
x_684 = lean_unbox(x_659);
lean_dec(x_659);
x_685 = lean_unbox(x_662);
lean_dec(x_662);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_686 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_680, x_677, x_20, x_653, x_655, x_683, x_684, x_661, x_685, x_682, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
x_690 = lean_ctor_get(x_687, 0);
lean_inc(x_690);
lean_dec(x_687);
if (lean_is_scalar(x_689)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_689;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_688);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; size_t x_694; size_t x_695; 
x_692 = lean_ctor_get(x_686, 1);
lean_inc(x_692);
lean_dec(x_686);
x_693 = lean_ctor_get(x_687, 0);
lean_inc(x_693);
lean_dec(x_687);
x_694 = 1;
x_695 = lean_usize_add(x_8, x_694);
x_8 = x_695;
x_9 = x_693;
x_17 = x_692;
goto _start;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_697 = lean_ctor_get(x_686, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_686, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_699 = x_686;
} else {
 lean_dec_ref(x_686);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
else
{
lean_object* x_701; uint8_t x_702; 
x_701 = lean_array_get_size(x_3);
x_702 = lean_nat_dec_lt(x_661, x_701);
lean_dec(x_701);
if (x_702 == 0)
{
lean_object* x_703; uint8_t x_704; uint8_t x_705; uint8_t x_706; lean_object* x_707; 
lean_dec(x_663);
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
x_703 = lean_box(0);
x_704 = lean_unbox(x_657);
lean_dec(x_657);
x_705 = lean_unbox(x_659);
lean_dec(x_659);
x_706 = lean_unbox(x_662);
lean_dec(x_662);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_707 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_680, x_677, x_20, x_653, x_655, x_704, x_705, x_661, x_706, x_703, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_710 = x_707;
} else {
 lean_dec_ref(x_707);
 x_710 = lean_box(0);
}
x_711 = lean_ctor_get(x_708, 0);
lean_inc(x_711);
lean_dec(x_708);
if (lean_is_scalar(x_710)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_710;
}
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_709);
return x_712;
}
else
{
lean_object* x_713; lean_object* x_714; size_t x_715; size_t x_716; 
x_713 = lean_ctor_get(x_707, 1);
lean_inc(x_713);
lean_dec(x_707);
x_714 = lean_ctor_get(x_708, 0);
lean_inc(x_714);
lean_dec(x_708);
x_715 = 1;
x_716 = lean_usize_add(x_8, x_715);
x_8 = x_716;
x_9 = x_714;
x_17 = x_713;
goto _start;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_718 = lean_ctor_get(x_707, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_707, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_720 = x_707;
} else {
 lean_dec_ref(x_707);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
else
{
lean_object* x_722; uint8_t x_723; 
x_722 = lean_array_fget(x_3, x_661);
x_723 = l_Lean_Meta_ParamInfo_isInstImplicit(x_722);
lean_dec(x_722);
if (x_723 == 0)
{
lean_object* x_724; uint8_t x_725; uint8_t x_726; uint8_t x_727; lean_object* x_728; 
lean_dec(x_663);
lean_dec(x_660);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_654);
x_724 = lean_box(0);
x_725 = lean_unbox(x_657);
lean_dec(x_657);
x_726 = lean_unbox(x_659);
lean_dec(x_659);
x_727 = lean_unbox(x_662);
lean_dec(x_662);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_728 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_680, x_677, x_20, x_653, x_655, x_725, x_726, x_661, x_727, x_724, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_731 = x_728;
} else {
 lean_dec_ref(x_728);
 x_731 = lean_box(0);
}
x_732 = lean_ctor_get(x_729, 0);
lean_inc(x_732);
lean_dec(x_729);
if (lean_is_scalar(x_731)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_731;
}
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_730);
return x_733;
}
else
{
lean_object* x_734; lean_object* x_735; size_t x_736; size_t x_737; 
x_734 = lean_ctor_get(x_728, 1);
lean_inc(x_734);
lean_dec(x_728);
x_735 = lean_ctor_get(x_729, 0);
lean_inc(x_735);
lean_dec(x_729);
x_736 = 1;
x_737 = lean_usize_add(x_8, x_736);
x_8 = x_737;
x_9 = x_735;
x_17 = x_734;
goto _start;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_739 = lean_ctor_get(x_728, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_728, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_741 = x_728;
} else {
 lean_dec_ref(x_728);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; size_t x_751; size_t x_752; 
x_743 = lean_array_push(x_655, x_20);
x_744 = lean_nat_add(x_661, x_678);
lean_dec(x_661);
if (lean_is_scalar(x_663)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_663;
}
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_662);
if (lean_is_scalar(x_660)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_660;
}
lean_ctor_set(x_746, 0, x_659);
lean_ctor_set(x_746, 1, x_745);
if (lean_is_scalar(x_658)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_658;
}
lean_ctor_set(x_747, 0, x_657);
lean_ctor_set(x_747, 1, x_746);
if (lean_is_scalar(x_656)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_656;
}
lean_ctor_set(x_748, 0, x_743);
lean_ctor_set(x_748, 1, x_747);
if (lean_is_scalar(x_654)) {
 x_749 = lean_alloc_ctor(0, 2, 0);
} else {
 x_749 = x_654;
}
lean_ctor_set(x_749, 0, x_653);
lean_ctor_set(x_749, 1, x_748);
x_750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_750, 0, x_680);
lean_ctor_set(x_750, 1, x_749);
x_751 = 1;
x_752 = lean_usize_add(x_8, x_751);
x_8 = x_752;
x_9 = x_750;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(707u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_19 = lean_array_uget(x_5, x_7);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_35, 2);
lean_inc(x_51);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_19);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_29);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_20 = x_54;
x_21 = x_16;
goto block_28;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_56 = lean_ctor_get(x_35, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_35, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_35, 0);
lean_dec(x_58);
x_59 = lean_array_fget(x_49, x_50);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_50, x_61);
lean_dec(x_50);
lean_ctor_set(x_35, 1, x_62);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_38, 2);
lean_inc(x_65);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_19);
lean_inc(x_4);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_29);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_20 = x_68;
x_21 = x_16;
goto block_28;
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_38);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_38, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_38, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_38, 0);
lean_dec(x_72);
x_73 = lean_array_fget(x_63, x_64);
x_74 = lean_nat_add(x_64, x_61);
lean_dec(x_64);
lean_ctor_set(x_38, 1, x_74);
lean_inc(x_19);
x_75 = l_Lean_Expr_app___override(x_44, x_19);
x_76 = l_Lean_Expr_bindingBody_x21(x_48);
lean_dec(x_48);
x_77 = lean_box(x_60);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_19);
x_78 = lean_array_push(x_47, x_73);
lean_ctor_set(x_33, 1, x_76);
lean_ctor_set(x_33, 0, x_78);
lean_ctor_set(x_32, 0, x_75);
lean_inc(x_4);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_29);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_20 = x_80;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_73);
lean_inc(x_19);
x_81 = lean_array_push(x_47, x_19);
x_82 = lean_array_get_size(x_3);
x_83 = lean_nat_dec_lt(x_41, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l_Lean_Meta_Simp_instInhabitedResult;
x_85 = l_outOfBounds___rarg(x_84);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_85);
x_86 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_85, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_nat_add(x_41, x_61);
lean_dec(x_41);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
lean_inc(x_87);
lean_inc(x_90);
x_91 = l_Lean_mkAppB(x_75, x_90, x_87);
x_92 = lean_array_push(x_81, x_90);
x_93 = lean_array_push(x_92, x_87);
x_94 = l_Lean_Expr_bindingBody_x21(x_76);
lean_dec(x_76);
x_95 = l_Lean_Expr_bindingBody_x21(x_94);
lean_dec(x_94);
lean_ctor_set(x_33, 1, x_95);
lean_ctor_set(x_33, 0, x_93);
lean_ctor_set(x_32, 0, x_91);
lean_ctor_set(x_31, 0, x_89);
lean_inc(x_4);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_29);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_20 = x_97;
x_21 = x_88;
goto block_28;
}
else
{
uint8_t x_98; 
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_86);
if (x_98 == 0)
{
return x_86;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_86, 0);
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_86);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_array_fget(x_3, x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_102);
x_103 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_102, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_nat_add(x_41, x_61);
lean_dec(x_41);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
lean_inc(x_104);
lean_inc(x_107);
x_108 = l_Lean_mkAppB(x_75, x_107, x_104);
x_109 = lean_array_push(x_81, x_107);
x_110 = lean_array_push(x_109, x_104);
x_111 = l_Lean_Expr_bindingBody_x21(x_76);
lean_dec(x_76);
x_112 = l_Lean_Expr_bindingBody_x21(x_111);
lean_dec(x_111);
lean_ctor_set(x_33, 1, x_112);
lean_ctor_set(x_33, 0, x_110);
lean_ctor_set(x_32, 0, x_108);
lean_ctor_set(x_31, 0, x_106);
lean_inc(x_4);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_29);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_20 = x_114;
x_21 = x_105;
goto block_28;
}
else
{
uint8_t x_115; 
lean_dec(x_102);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_103);
if (x_115 == 0)
{
return x_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_103, 0);
x_117 = lean_ctor_get(x_103, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_103);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
case 3:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_73);
x_119 = lean_array_push(x_47, x_19);
lean_ctor_set(x_33, 1, x_76);
lean_ctor_set(x_33, 0, x_119);
lean_ctor_set(x_32, 0, x_75);
lean_inc(x_4);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_4);
lean_ctor_set(x_120, 1, x_29);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_20 = x_121;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_73);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_122 = lean_array_push(x_47, x_19);
x_123 = l_Lean_Expr_bindingDomain_x21(x_76);
x_124 = lean_expr_instantiate_rev(x_123, x_122);
lean_dec(x_123);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_125 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_124);
x_128 = l_Lean_Meta_isExprDefEq(x_126, x_124, x_12, x_13, x_14, x_15, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_19);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_124);
x_133 = l_Lean_Meta_trySynthInstance(x_124, x_132, x_12, x_13, x_14, x_15, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_124);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_4);
x_137 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_35, x_38, x_4, x_75, x_122, x_76, x_136, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_135);
lean_dec(x_76);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_20 = x_138;
x_21 = x_139;
goto block_28;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_134);
x_140 = lean_ctor_get(x_133, 1);
lean_inc(x_140);
lean_dec(x_133);
x_141 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_142 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_141, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_140);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_124);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_box(0);
x_147 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_132, x_122, x_76, x_75, x_41, x_35, x_38, x_146, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_20 = x_148;
x_21 = x_149;
goto block_28;
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_151 = lean_ctor_get(x_142, 1);
x_152 = lean_ctor_get(x_142, 0);
lean_dec(x_152);
x_153 = l_Lean_indentExpr(x_124);
x_154 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
lean_ctor_set_tag(x_142, 7);
lean_ctor_set(x_142, 1, x_153);
lean_ctor_set(x_142, 0, x_154);
x_155 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_142);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_141, x_156, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_151);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_132, x_122, x_76, x_75, x_41, x_35, x_38, x_158, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_159);
lean_dec(x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_20 = x_161;
x_21 = x_162;
goto block_28;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_163 = lean_ctor_get(x_142, 1);
lean_inc(x_163);
lean_dec(x_142);
x_164 = l_Lean_indentExpr(x_124);
x_165 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_141, x_168, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_163);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_132, x_122, x_76, x_75, x_41, x_35, x_38, x_170, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_171);
lean_dec(x_170);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_20 = x_173;
x_21 = x_174;
goto block_28;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_133);
if (x_175 == 0)
{
return x_133;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_133, 0);
x_177 = lean_ctor_get(x_133, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_133);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_124);
x_179 = lean_ctor_get(x_128, 1);
lean_inc(x_179);
lean_dec(x_128);
lean_inc(x_4);
x_180 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_35, x_38, x_4, x_75, x_122, x_76, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_179);
lean_dec(x_76);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_20 = x_181;
x_21 = x_182;
goto block_28;
}
}
else
{
uint8_t x_183; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_183 = !lean_is_exclusive(x_128);
if (x_183 == 0)
{
return x_128;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_128, 0);
x_185 = lean_ctor_get(x_128, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_128);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_187 = !lean_is_exclusive(x_125);
if (x_187 == 0)
{
return x_125;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_125, 0);
x_189 = lean_ctor_get(x_125, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_125);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
default: 
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_19);
x_191 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_192 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_191, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
lean_ctor_set(x_33, 1, x_76);
lean_ctor_set(x_32, 0, x_75);
lean_inc(x_4);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_4);
lean_ctor_set(x_194, 1, x_29);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_20 = x_195;
x_21 = x_193;
goto block_28;
}
else
{
uint8_t x_196; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_38);
lean_dec(x_35);
lean_free_object(x_33);
lean_dec(x_47);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_192, 0);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_192);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_38);
x_200 = lean_array_fget(x_63, x_64);
x_201 = lean_nat_add(x_64, x_61);
lean_dec(x_64);
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_63);
lean_ctor_set(x_202, 1, x_201);
lean_ctor_set(x_202, 2, x_65);
lean_inc(x_19);
x_203 = l_Lean_Expr_app___override(x_44, x_19);
x_204 = l_Lean_Expr_bindingBody_x21(x_48);
lean_dec(x_48);
x_205 = lean_box(x_60);
switch (lean_obj_tag(x_205)) {
case 0:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_19);
x_206 = lean_array_push(x_47, x_200);
lean_ctor_set(x_33, 1, x_204);
lean_ctor_set(x_33, 0, x_206);
lean_ctor_set(x_32, 0, x_203);
lean_ctor_set(x_29, 0, x_202);
lean_inc(x_4);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_4);
lean_ctor_set(x_207, 1, x_29);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_20 = x_208;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec(x_200);
lean_inc(x_19);
x_209 = lean_array_push(x_47, x_19);
x_210 = lean_array_get_size(x_3);
x_211 = lean_nat_dec_lt(x_41, x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = l_Lean_Meta_Simp_instInhabitedResult;
x_213 = l_outOfBounds___rarg(x_212);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_213);
x_214 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_213, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_nat_add(x_41, x_61);
lean_dec(x_41);
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
lean_dec(x_213);
lean_inc(x_215);
lean_inc(x_218);
x_219 = l_Lean_mkAppB(x_203, x_218, x_215);
x_220 = lean_array_push(x_209, x_218);
x_221 = lean_array_push(x_220, x_215);
x_222 = l_Lean_Expr_bindingBody_x21(x_204);
lean_dec(x_204);
x_223 = l_Lean_Expr_bindingBody_x21(x_222);
lean_dec(x_222);
lean_ctor_set(x_33, 1, x_223);
lean_ctor_set(x_33, 0, x_221);
lean_ctor_set(x_32, 0, x_219);
lean_ctor_set(x_31, 0, x_217);
lean_ctor_set(x_29, 0, x_202);
lean_inc(x_4);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_4);
lean_ctor_set(x_224, 1, x_29);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_20 = x_225;
x_21 = x_216;
goto block_28;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_213);
lean_dec(x_209);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_226 = lean_ctor_get(x_214, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_214, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_228 = x_214;
} else {
 lean_dec_ref(x_214);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_array_fget(x_3, x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_230);
x_231 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_230, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_nat_add(x_41, x_61);
lean_dec(x_41);
x_235 = lean_ctor_get(x_230, 0);
lean_inc(x_235);
lean_dec(x_230);
lean_inc(x_232);
lean_inc(x_235);
x_236 = l_Lean_mkAppB(x_203, x_235, x_232);
x_237 = lean_array_push(x_209, x_235);
x_238 = lean_array_push(x_237, x_232);
x_239 = l_Lean_Expr_bindingBody_x21(x_204);
lean_dec(x_204);
x_240 = l_Lean_Expr_bindingBody_x21(x_239);
lean_dec(x_239);
lean_ctor_set(x_33, 1, x_240);
lean_ctor_set(x_33, 0, x_238);
lean_ctor_set(x_32, 0, x_236);
lean_ctor_set(x_31, 0, x_234);
lean_ctor_set(x_29, 0, x_202);
lean_inc(x_4);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_4);
lean_ctor_set(x_241, 1, x_29);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_20 = x_242;
x_21 = x_233;
goto block_28;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_230);
lean_dec(x_209);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_243 = lean_ctor_get(x_231, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_231, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_245 = x_231;
} else {
 lean_dec_ref(x_231);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
case 3:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_200);
x_247 = lean_array_push(x_47, x_19);
lean_ctor_set(x_33, 1, x_204);
lean_ctor_set(x_33, 0, x_247);
lean_ctor_set(x_32, 0, x_203);
lean_ctor_set(x_29, 0, x_202);
lean_inc(x_4);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_4);
lean_ctor_set(x_248, 1, x_29);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_20 = x_249;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_200);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_250 = lean_array_push(x_47, x_19);
x_251 = l_Lean_Expr_bindingDomain_x21(x_204);
x_252 = lean_expr_instantiate_rev(x_251, x_250);
lean_dec(x_251);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_253 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_252);
x_256 = l_Lean_Meta_isExprDefEq(x_254, x_252, x_12, x_13, x_14, x_15, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_19);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_252);
x_261 = l_Lean_Meta_trySynthInstance(x_252, x_260, x_12, x_13, x_14, x_15, x_259);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 1)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_252);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
lean_dec(x_262);
lean_inc(x_4);
x_265 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_35, x_202, x_4, x_203, x_250, x_204, x_264, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_263);
lean_dec(x_204);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_20 = x_266;
x_21 = x_267;
goto block_28;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_262);
x_268 = lean_ctor_get(x_261, 1);
lean_inc(x_268);
lean_dec(x_261);
x_269 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_270 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_269, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_268);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_252);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_box(0);
x_275 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_260, x_250, x_204, x_203, x_41, x_35, x_202, x_274, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_273);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_20 = x_276;
x_21 = x_277;
goto block_28;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_278 = lean_ctor_get(x_270, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_279 = x_270;
} else {
 lean_dec_ref(x_270);
 x_279 = lean_box(0);
}
x_280 = l_Lean_indentExpr(x_252);
x_281 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_279)) {
 x_282 = lean_alloc_ctor(7, 2, 0);
} else {
 x_282 = x_279;
 lean_ctor_set_tag(x_282, 7);
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_269, x_284, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_278);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_260, x_250, x_204, x_203, x_41, x_35, x_202, x_286, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_287);
lean_dec(x_286);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_20 = x_289;
x_21 = x_290;
goto block_28;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_291 = lean_ctor_get(x_261, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_261, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_293 = x_261;
} else {
 lean_dec_ref(x_261);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_252);
x_295 = lean_ctor_get(x_256, 1);
lean_inc(x_295);
lean_dec(x_256);
lean_inc(x_4);
x_296 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_35, x_202, x_4, x_203, x_250, x_204, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_295);
lean_dec(x_204);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_20 = x_297;
x_21 = x_298;
goto block_28;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_299 = lean_ctor_get(x_256, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_256, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_301 = x_256;
} else {
 lean_dec_ref(x_256);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_303 = lean_ctor_get(x_253, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_253, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_305 = x_253;
} else {
 lean_dec_ref(x_253);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
default: 
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_205);
lean_dec(x_200);
lean_dec(x_19);
x_307 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_308 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_307, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
lean_ctor_set(x_33, 1, x_204);
lean_ctor_set(x_32, 0, x_203);
lean_ctor_set(x_29, 0, x_202);
lean_inc(x_4);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_4);
lean_ctor_set(x_310, 1, x_29);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_20 = x_311;
x_21 = x_309;
goto block_28;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_35);
lean_free_object(x_33);
lean_dec(x_47);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_314 = x_308;
} else {
 lean_dec_ref(x_308);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
}
}
}
}
else
{
lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_35);
x_316 = lean_array_fget(x_49, x_50);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
x_318 = lean_unsigned_to_nat(1u);
x_319 = lean_nat_add(x_50, x_318);
lean_dec(x_50);
x_320 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_320, 0, x_49);
lean_ctor_set(x_320, 1, x_319);
lean_ctor_set(x_320, 2, x_51);
x_321 = lean_ctor_get(x_38, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_38, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_38, 2);
lean_inc(x_323);
x_324 = lean_nat_dec_lt(x_322, x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_19);
lean_ctor_set(x_30, 0, x_320);
lean_inc(x_4);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_4);
lean_ctor_set(x_325, 1, x_29);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_20 = x_326;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_327 = x_38;
} else {
 lean_dec_ref(x_38);
 x_327 = lean_box(0);
}
x_328 = lean_array_fget(x_321, x_322);
x_329 = lean_nat_add(x_322, x_318);
lean_dec(x_322);
if (lean_is_scalar(x_327)) {
 x_330 = lean_alloc_ctor(0, 3, 0);
} else {
 x_330 = x_327;
}
lean_ctor_set(x_330, 0, x_321);
lean_ctor_set(x_330, 1, x_329);
lean_ctor_set(x_330, 2, x_323);
lean_inc(x_19);
x_331 = l_Lean_Expr_app___override(x_44, x_19);
x_332 = l_Lean_Expr_bindingBody_x21(x_48);
lean_dec(x_48);
x_333 = lean_box(x_317);
switch (lean_obj_tag(x_333)) {
case 0:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_19);
x_334 = lean_array_push(x_47, x_328);
lean_ctor_set(x_33, 1, x_332);
lean_ctor_set(x_33, 0, x_334);
lean_ctor_set(x_32, 0, x_331);
lean_ctor_set(x_30, 0, x_320);
lean_ctor_set(x_29, 0, x_330);
lean_inc(x_4);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_4);
lean_ctor_set(x_335, 1, x_29);
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_20 = x_336;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_dec(x_328);
lean_inc(x_19);
x_337 = lean_array_push(x_47, x_19);
x_338 = lean_array_get_size(x_3);
x_339 = lean_nat_dec_lt(x_41, x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = l_Lean_Meta_Simp_instInhabitedResult;
x_341 = l_outOfBounds___rarg(x_340);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_341);
x_342 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_341, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_nat_add(x_41, x_318);
lean_dec(x_41);
x_346 = lean_ctor_get(x_341, 0);
lean_inc(x_346);
lean_dec(x_341);
lean_inc(x_343);
lean_inc(x_346);
x_347 = l_Lean_mkAppB(x_331, x_346, x_343);
x_348 = lean_array_push(x_337, x_346);
x_349 = lean_array_push(x_348, x_343);
x_350 = l_Lean_Expr_bindingBody_x21(x_332);
lean_dec(x_332);
x_351 = l_Lean_Expr_bindingBody_x21(x_350);
lean_dec(x_350);
lean_ctor_set(x_33, 1, x_351);
lean_ctor_set(x_33, 0, x_349);
lean_ctor_set(x_32, 0, x_347);
lean_ctor_set(x_31, 0, x_345);
lean_ctor_set(x_30, 0, x_320);
lean_ctor_set(x_29, 0, x_330);
lean_inc(x_4);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_4);
lean_ctor_set(x_352, 1, x_29);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_352);
x_20 = x_353;
x_21 = x_344;
goto block_28;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_341);
lean_dec(x_337);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_356 = x_342;
} else {
 lean_dec_ref(x_342);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_array_fget(x_3, x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_358);
x_359 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_358, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_nat_add(x_41, x_318);
lean_dec(x_41);
x_363 = lean_ctor_get(x_358, 0);
lean_inc(x_363);
lean_dec(x_358);
lean_inc(x_360);
lean_inc(x_363);
x_364 = l_Lean_mkAppB(x_331, x_363, x_360);
x_365 = lean_array_push(x_337, x_363);
x_366 = lean_array_push(x_365, x_360);
x_367 = l_Lean_Expr_bindingBody_x21(x_332);
lean_dec(x_332);
x_368 = l_Lean_Expr_bindingBody_x21(x_367);
lean_dec(x_367);
lean_ctor_set(x_33, 1, x_368);
lean_ctor_set(x_33, 0, x_366);
lean_ctor_set(x_32, 0, x_364);
lean_ctor_set(x_31, 0, x_362);
lean_ctor_set(x_30, 0, x_320);
lean_ctor_set(x_29, 0, x_330);
lean_inc(x_4);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_4);
lean_ctor_set(x_369, 1, x_29);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_369);
x_20 = x_370;
x_21 = x_361;
goto block_28;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_358);
lean_dec(x_337);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_371 = lean_ctor_get(x_359, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_359, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_373 = x_359;
} else {
 lean_dec_ref(x_359);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
}
case 3:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_328);
x_375 = lean_array_push(x_47, x_19);
lean_ctor_set(x_33, 1, x_332);
lean_ctor_set(x_33, 0, x_375);
lean_ctor_set(x_32, 0, x_331);
lean_ctor_set(x_30, 0, x_320);
lean_ctor_set(x_29, 0, x_330);
lean_inc(x_4);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_4);
lean_ctor_set(x_376, 1, x_29);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_376);
x_20 = x_377;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_328);
lean_free_object(x_33);
lean_free_object(x_32);
lean_free_object(x_31);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_378 = lean_array_push(x_47, x_19);
x_379 = l_Lean_Expr_bindingDomain_x21(x_332);
x_380 = lean_expr_instantiate_rev(x_379, x_378);
lean_dec(x_379);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_381 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_380);
x_384 = l_Lean_Meta_isExprDefEq(x_382, x_380, x_12, x_13, x_14, x_15, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_unbox(x_385);
lean_dec(x_385);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_19);
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
lean_dec(x_384);
x_388 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_380);
x_389 = l_Lean_Meta_trySynthInstance(x_380, x_388, x_12, x_13, x_14, x_15, x_387);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 1)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_380);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_ctor_get(x_390, 0);
lean_inc(x_392);
lean_dec(x_390);
lean_inc(x_4);
x_393 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_320, x_330, x_4, x_331, x_378, x_332, x_392, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_391);
lean_dec(x_332);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_20 = x_394;
x_21 = x_395;
goto block_28;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
lean_dec(x_390);
x_396 = lean_ctor_get(x_389, 1);
lean_inc(x_396);
lean_dec(x_389);
x_397 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_398 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_396);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_unbox(x_399);
lean_dec(x_399);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_380);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
lean_dec(x_398);
x_402 = lean_box(0);
x_403 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_388, x_378, x_332, x_331, x_41, x_320, x_330, x_402, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_401);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_20 = x_404;
x_21 = x_405;
goto block_28;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_406 = lean_ctor_get(x_398, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_407 = x_398;
} else {
 lean_dec_ref(x_398);
 x_407 = lean_box(0);
}
x_408 = l_Lean_indentExpr(x_380);
x_409 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_407)) {
 x_410 = lean_alloc_ctor(7, 2, 0);
} else {
 x_410 = x_407;
 lean_ctor_set_tag(x_410, 7);
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
x_411 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_397, x_412, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_406);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_388, x_378, x_332, x_331, x_41, x_320, x_330, x_414, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_415);
lean_dec(x_414);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_20 = x_417;
x_21 = x_418;
goto block_28;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_419 = lean_ctor_get(x_389, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_389, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_421 = x_389;
} else {
 lean_dec_ref(x_389);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_380);
x_423 = lean_ctor_get(x_384, 1);
lean_inc(x_423);
lean_dec(x_384);
lean_inc(x_4);
x_424 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_320, x_330, x_4, x_331, x_378, x_332, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_423);
lean_dec(x_332);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_20 = x_425;
x_21 = x_426;
goto block_28;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_427 = lean_ctor_get(x_384, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_384, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_429 = x_384;
} else {
 lean_dec_ref(x_384);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_431 = lean_ctor_get(x_381, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_381, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_433 = x_381;
} else {
 lean_dec_ref(x_381);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
default: 
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_19);
x_435 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_436 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_435, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
lean_dec(x_436);
lean_ctor_set(x_33, 1, x_332);
lean_ctor_set(x_32, 0, x_331);
lean_ctor_set(x_30, 0, x_320);
lean_ctor_set(x_29, 0, x_330);
lean_inc(x_4);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_4);
lean_ctor_set(x_438, 1, x_29);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_438);
x_20 = x_439;
x_21 = x_437;
goto block_28;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_320);
lean_free_object(x_33);
lean_dec(x_47);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_440 = lean_ctor_get(x_436, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_436, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_442 = x_436;
} else {
 lean_dec_ref(x_436);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_444 = lean_ctor_get(x_33, 0);
x_445 = lean_ctor_get(x_33, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_33);
x_446 = lean_ctor_get(x_35, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_35, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_35, 2);
lean_inc(x_448);
x_449 = lean_nat_dec_lt(x_447, x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_19);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_444);
lean_ctor_set(x_450, 1, x_445);
lean_ctor_set(x_32, 1, x_450);
lean_inc(x_4);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_4);
lean_ctor_set(x_451, 1, x_29);
x_452 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_452, 0, x_451);
x_20 = x_452;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_453 = x_35;
} else {
 lean_dec_ref(x_35);
 x_453 = lean_box(0);
}
x_454 = lean_array_fget(x_446, x_447);
x_455 = lean_unbox(x_454);
lean_dec(x_454);
x_456 = lean_unsigned_to_nat(1u);
x_457 = lean_nat_add(x_447, x_456);
lean_dec(x_447);
if (lean_is_scalar(x_453)) {
 x_458 = lean_alloc_ctor(0, 3, 0);
} else {
 x_458 = x_453;
}
lean_ctor_set(x_458, 0, x_446);
lean_ctor_set(x_458, 1, x_457);
lean_ctor_set(x_458, 2, x_448);
x_459 = lean_ctor_get(x_38, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_38, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_38, 2);
lean_inc(x_461);
x_462 = lean_nat_dec_lt(x_460, x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_19);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_444);
lean_ctor_set(x_463, 1, x_445);
lean_ctor_set(x_32, 1, x_463);
lean_ctor_set(x_30, 0, x_458);
lean_inc(x_4);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_4);
lean_ctor_set(x_464, 1, x_29);
x_465 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_465, 0, x_464);
x_20 = x_465;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_466 = x_38;
} else {
 lean_dec_ref(x_38);
 x_466 = lean_box(0);
}
x_467 = lean_array_fget(x_459, x_460);
x_468 = lean_nat_add(x_460, x_456);
lean_dec(x_460);
if (lean_is_scalar(x_466)) {
 x_469 = lean_alloc_ctor(0, 3, 0);
} else {
 x_469 = x_466;
}
lean_ctor_set(x_469, 0, x_459);
lean_ctor_set(x_469, 1, x_468);
lean_ctor_set(x_469, 2, x_461);
lean_inc(x_19);
x_470 = l_Lean_Expr_app___override(x_44, x_19);
x_471 = l_Lean_Expr_bindingBody_x21(x_445);
lean_dec(x_445);
x_472 = lean_box(x_455);
switch (lean_obj_tag(x_472)) {
case 0:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_19);
x_473 = lean_array_push(x_444, x_467);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_471);
lean_ctor_set(x_32, 1, x_474);
lean_ctor_set(x_32, 0, x_470);
lean_ctor_set(x_30, 0, x_458);
lean_ctor_set(x_29, 0, x_469);
lean_inc(x_4);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_4);
lean_ctor_set(x_475, 1, x_29);
x_476 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_476, 0, x_475);
x_20 = x_476;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; 
lean_dec(x_467);
lean_inc(x_19);
x_477 = lean_array_push(x_444, x_19);
x_478 = lean_array_get_size(x_3);
x_479 = lean_nat_dec_lt(x_41, x_478);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = l_Lean_Meta_Simp_instInhabitedResult;
x_481 = l_outOfBounds___rarg(x_480);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_481);
x_482 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_481, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_nat_add(x_41, x_456);
lean_dec(x_41);
x_486 = lean_ctor_get(x_481, 0);
lean_inc(x_486);
lean_dec(x_481);
lean_inc(x_483);
lean_inc(x_486);
x_487 = l_Lean_mkAppB(x_470, x_486, x_483);
x_488 = lean_array_push(x_477, x_486);
x_489 = lean_array_push(x_488, x_483);
x_490 = l_Lean_Expr_bindingBody_x21(x_471);
lean_dec(x_471);
x_491 = l_Lean_Expr_bindingBody_x21(x_490);
lean_dec(x_490);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_491);
lean_ctor_set(x_32, 1, x_492);
lean_ctor_set(x_32, 0, x_487);
lean_ctor_set(x_31, 0, x_485);
lean_ctor_set(x_30, 0, x_458);
lean_ctor_set(x_29, 0, x_469);
lean_inc(x_4);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_4);
lean_ctor_set(x_493, 1, x_29);
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_20 = x_494;
x_21 = x_484;
goto block_28;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_481);
lean_dec(x_477);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_495 = lean_ctor_get(x_482, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_482, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_497 = x_482;
} else {
 lean_dec_ref(x_482);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
else
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_array_fget(x_3, x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_499);
x_500 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_499, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_nat_add(x_41, x_456);
lean_dec(x_41);
x_504 = lean_ctor_get(x_499, 0);
lean_inc(x_504);
lean_dec(x_499);
lean_inc(x_501);
lean_inc(x_504);
x_505 = l_Lean_mkAppB(x_470, x_504, x_501);
x_506 = lean_array_push(x_477, x_504);
x_507 = lean_array_push(x_506, x_501);
x_508 = l_Lean_Expr_bindingBody_x21(x_471);
lean_dec(x_471);
x_509 = l_Lean_Expr_bindingBody_x21(x_508);
lean_dec(x_508);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_509);
lean_ctor_set(x_32, 1, x_510);
lean_ctor_set(x_32, 0, x_505);
lean_ctor_set(x_31, 0, x_503);
lean_ctor_set(x_30, 0, x_458);
lean_ctor_set(x_29, 0, x_469);
lean_inc(x_4);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_4);
lean_ctor_set(x_511, 1, x_29);
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_511);
x_20 = x_512;
x_21 = x_502;
goto block_28;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_499);
lean_dec(x_477);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_513 = lean_ctor_get(x_500, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_500, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_515 = x_500;
} else {
 lean_dec_ref(x_500);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
}
case 3:
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_467);
x_517 = lean_array_push(x_444, x_19);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_471);
lean_ctor_set(x_32, 1, x_518);
lean_ctor_set(x_32, 0, x_470);
lean_ctor_set(x_30, 0, x_458);
lean_ctor_set(x_29, 0, x_469);
lean_inc(x_4);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_4);
lean_ctor_set(x_519, 1, x_29);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_519);
x_20 = x_520;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_467);
lean_free_object(x_32);
lean_free_object(x_31);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_521 = lean_array_push(x_444, x_19);
x_522 = l_Lean_Expr_bindingDomain_x21(x_471);
x_523 = lean_expr_instantiate_rev(x_522, x_521);
lean_dec(x_522);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_524 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_523);
x_527 = l_Lean_Meta_isExprDefEq(x_525, x_523, x_12, x_13, x_14, x_15, x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; uint8_t x_529; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_unbox(x_528);
lean_dec(x_528);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_19);
x_530 = lean_ctor_get(x_527, 1);
lean_inc(x_530);
lean_dec(x_527);
x_531 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_523);
x_532 = l_Lean_Meta_trySynthInstance(x_523, x_531, x_12, x_13, x_14, x_15, x_530);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
if (lean_obj_tag(x_533) == 1)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_523);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_4);
x_536 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_458, x_469, x_4, x_470, x_521, x_471, x_535, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_534);
lean_dec(x_471);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_20 = x_537;
x_21 = x_538;
goto block_28;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
lean_dec(x_533);
x_539 = lean_ctor_get(x_532, 1);
lean_inc(x_539);
lean_dec(x_532);
x_540 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_541 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_540, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_539);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_523);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec(x_541);
x_545 = lean_box(0);
x_546 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_531, x_521, x_471, x_470, x_41, x_458, x_469, x_545, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_544);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_20 = x_547;
x_21 = x_548;
goto block_28;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_549 = lean_ctor_get(x_541, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_550 = x_541;
} else {
 lean_dec_ref(x_541);
 x_550 = lean_box(0);
}
x_551 = l_Lean_indentExpr(x_523);
x_552 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_550)) {
 x_553 = lean_alloc_ctor(7, 2, 0);
} else {
 x_553 = x_550;
 lean_ctor_set_tag(x_553, 7);
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_551);
x_554 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_540, x_555, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_549);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_531, x_521, x_471, x_470, x_41, x_458, x_469, x_557, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_558);
lean_dec(x_557);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_20 = x_560;
x_21 = x_561;
goto block_28;
}
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_562 = lean_ctor_get(x_532, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_532, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_564 = x_532;
} else {
 lean_dec_ref(x_532);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_523);
x_566 = lean_ctor_get(x_527, 1);
lean_inc(x_566);
lean_dec(x_527);
lean_inc(x_4);
x_567 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_458, x_469, x_4, x_470, x_521, x_471, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_566);
lean_dec(x_471);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
x_20 = x_568;
x_21 = x_569;
goto block_28;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_570 = lean_ctor_get(x_527, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_527, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_572 = x_527;
} else {
 lean_dec_ref(x_527);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_571);
return x_573;
}
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_574 = lean_ctor_get(x_524, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_524, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_576 = x_524;
} else {
 lean_dec_ref(x_524);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
}
default: 
{
lean_object* x_578; lean_object* x_579; 
lean_dec(x_472);
lean_dec(x_467);
lean_dec(x_19);
x_578 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_579 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_578, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_444);
lean_ctor_set(x_581, 1, x_471);
lean_ctor_set(x_32, 1, x_581);
lean_ctor_set(x_32, 0, x_470);
lean_ctor_set(x_30, 0, x_458);
lean_ctor_set(x_29, 0, x_469);
lean_inc(x_4);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_4);
lean_ctor_set(x_582, 1, x_29);
x_583 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_583, 0, x_582);
x_20 = x_583;
x_21 = x_580;
goto block_28;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_458);
lean_dec(x_444);
lean_free_object(x_32);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_584 = lean_ctor_get(x_579, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_579, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_586 = x_579;
} else {
 lean_dec_ref(x_579);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(1, 2, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
}
}
}
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_588 = lean_ctor_get(x_32, 0);
lean_inc(x_588);
lean_dec(x_32);
x_589 = lean_ctor_get(x_33, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_33, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_591 = x_33;
} else {
 lean_dec_ref(x_33);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_35, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_35, 1);
lean_inc(x_593);
x_594 = lean_ctor_get(x_35, 2);
lean_inc(x_594);
x_595 = lean_nat_dec_lt(x_593, x_594);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_19);
if (lean_is_scalar(x_591)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_591;
}
lean_ctor_set(x_596, 0, x_589);
lean_ctor_set(x_596, 1, x_590);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_588);
lean_ctor_set(x_597, 1, x_596);
lean_ctor_set(x_31, 1, x_597);
lean_inc(x_4);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_4);
lean_ctor_set(x_598, 1, x_29);
x_599 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_20 = x_599;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_600 = x_35;
} else {
 lean_dec_ref(x_35);
 x_600 = lean_box(0);
}
x_601 = lean_array_fget(x_592, x_593);
x_602 = lean_unbox(x_601);
lean_dec(x_601);
x_603 = lean_unsigned_to_nat(1u);
x_604 = lean_nat_add(x_593, x_603);
lean_dec(x_593);
if (lean_is_scalar(x_600)) {
 x_605 = lean_alloc_ctor(0, 3, 0);
} else {
 x_605 = x_600;
}
lean_ctor_set(x_605, 0, x_592);
lean_ctor_set(x_605, 1, x_604);
lean_ctor_set(x_605, 2, x_594);
x_606 = lean_ctor_get(x_38, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_38, 1);
lean_inc(x_607);
x_608 = lean_ctor_get(x_38, 2);
lean_inc(x_608);
x_609 = lean_nat_dec_lt(x_607, x_608);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_608);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_19);
if (lean_is_scalar(x_591)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_591;
}
lean_ctor_set(x_610, 0, x_589);
lean_ctor_set(x_610, 1, x_590);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_588);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_31, 1, x_611);
lean_ctor_set(x_30, 0, x_605);
lean_inc(x_4);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_4);
lean_ctor_set(x_612, 1, x_29);
x_613 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_613, 0, x_612);
x_20 = x_613;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_614 = x_38;
} else {
 lean_dec_ref(x_38);
 x_614 = lean_box(0);
}
x_615 = lean_array_fget(x_606, x_607);
x_616 = lean_nat_add(x_607, x_603);
lean_dec(x_607);
if (lean_is_scalar(x_614)) {
 x_617 = lean_alloc_ctor(0, 3, 0);
} else {
 x_617 = x_614;
}
lean_ctor_set(x_617, 0, x_606);
lean_ctor_set(x_617, 1, x_616);
lean_ctor_set(x_617, 2, x_608);
lean_inc(x_19);
x_618 = l_Lean_Expr_app___override(x_588, x_19);
x_619 = l_Lean_Expr_bindingBody_x21(x_590);
lean_dec(x_590);
x_620 = lean_box(x_602);
switch (lean_obj_tag(x_620)) {
case 0:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_19);
x_621 = lean_array_push(x_589, x_615);
if (lean_is_scalar(x_591)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_591;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_619);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_618);
lean_ctor_set(x_623, 1, x_622);
lean_ctor_set(x_31, 1, x_623);
lean_ctor_set(x_30, 0, x_605);
lean_ctor_set(x_29, 0, x_617);
lean_inc(x_4);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_4);
lean_ctor_set(x_624, 1, x_29);
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_624);
x_20 = x_625;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec(x_615);
lean_inc(x_19);
x_626 = lean_array_push(x_589, x_19);
x_627 = lean_array_get_size(x_3);
x_628 = lean_nat_dec_lt(x_41, x_627);
lean_dec(x_627);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = l_Lean_Meta_Simp_instInhabitedResult;
x_630 = l_outOfBounds___rarg(x_629);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_630);
x_631 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_630, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_nat_add(x_41, x_603);
lean_dec(x_41);
x_635 = lean_ctor_get(x_630, 0);
lean_inc(x_635);
lean_dec(x_630);
lean_inc(x_632);
lean_inc(x_635);
x_636 = l_Lean_mkAppB(x_618, x_635, x_632);
x_637 = lean_array_push(x_626, x_635);
x_638 = lean_array_push(x_637, x_632);
x_639 = l_Lean_Expr_bindingBody_x21(x_619);
lean_dec(x_619);
x_640 = l_Lean_Expr_bindingBody_x21(x_639);
lean_dec(x_639);
if (lean_is_scalar(x_591)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_591;
}
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_636);
lean_ctor_set(x_642, 1, x_641);
lean_ctor_set(x_31, 1, x_642);
lean_ctor_set(x_31, 0, x_634);
lean_ctor_set(x_30, 0, x_605);
lean_ctor_set(x_29, 0, x_617);
lean_inc(x_4);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_4);
lean_ctor_set(x_643, 1, x_29);
x_644 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_20 = x_644;
x_21 = x_633;
goto block_28;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_630);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_591);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_645 = lean_ctor_get(x_631, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_631, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_647 = x_631;
} else {
 lean_dec_ref(x_631);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_array_fget(x_3, x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_649);
x_650 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_649, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
x_653 = lean_nat_add(x_41, x_603);
lean_dec(x_41);
x_654 = lean_ctor_get(x_649, 0);
lean_inc(x_654);
lean_dec(x_649);
lean_inc(x_651);
lean_inc(x_654);
x_655 = l_Lean_mkAppB(x_618, x_654, x_651);
x_656 = lean_array_push(x_626, x_654);
x_657 = lean_array_push(x_656, x_651);
x_658 = l_Lean_Expr_bindingBody_x21(x_619);
lean_dec(x_619);
x_659 = l_Lean_Expr_bindingBody_x21(x_658);
lean_dec(x_658);
if (lean_is_scalar(x_591)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_591;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_659);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_655);
lean_ctor_set(x_661, 1, x_660);
lean_ctor_set(x_31, 1, x_661);
lean_ctor_set(x_31, 0, x_653);
lean_ctor_set(x_30, 0, x_605);
lean_ctor_set(x_29, 0, x_617);
lean_inc(x_4);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_4);
lean_ctor_set(x_662, 1, x_29);
x_663 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_663, 0, x_662);
x_20 = x_663;
x_21 = x_652;
goto block_28;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_649);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_591);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_664 = lean_ctor_get(x_650, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_650, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 x_666 = x_650;
} else {
 lean_dec_ref(x_650);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
}
}
case 3:
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_615);
x_668 = lean_array_push(x_589, x_19);
if (lean_is_scalar(x_591)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_591;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_619);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_618);
lean_ctor_set(x_670, 1, x_669);
lean_ctor_set(x_31, 1, x_670);
lean_ctor_set(x_30, 0, x_605);
lean_ctor_set(x_29, 0, x_617);
lean_inc(x_4);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_4);
lean_ctor_set(x_671, 1, x_29);
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_671);
x_20 = x_672;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_615);
lean_dec(x_591);
lean_free_object(x_31);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_673 = lean_array_push(x_589, x_19);
x_674 = l_Lean_Expr_bindingDomain_x21(x_619);
x_675 = lean_expr_instantiate_rev(x_674, x_673);
lean_dec(x_674);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_676 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_675);
x_679 = l_Lean_Meta_isExprDefEq(x_677, x_675, x_12, x_13, x_14, x_15, x_678);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; uint8_t x_681; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_unbox(x_680);
lean_dec(x_680);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_19);
x_682 = lean_ctor_get(x_679, 1);
lean_inc(x_682);
lean_dec(x_679);
x_683 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_675);
x_684 = l_Lean_Meta_trySynthInstance(x_675, x_683, x_12, x_13, x_14, x_15, x_682);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
if (lean_obj_tag(x_685) == 1)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_675);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_ctor_get(x_685, 0);
lean_inc(x_687);
lean_dec(x_685);
lean_inc(x_4);
x_688 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_605, x_617, x_4, x_618, x_673, x_619, x_687, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_686);
lean_dec(x_619);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_20 = x_689;
x_21 = x_690;
goto block_28;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_685);
x_691 = lean_ctor_get(x_684, 1);
lean_inc(x_691);
lean_dec(x_684);
x_692 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_693 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_692, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_691);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_unbox(x_694);
lean_dec(x_694);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_675);
x_696 = lean_ctor_get(x_693, 1);
lean_inc(x_696);
lean_dec(x_693);
x_697 = lean_box(0);
x_698 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_683, x_673, x_619, x_618, x_41, x_605, x_617, x_697, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_696);
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
x_20 = x_699;
x_21 = x_700;
goto block_28;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_701 = lean_ctor_get(x_693, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_702 = x_693;
} else {
 lean_dec_ref(x_693);
 x_702 = lean_box(0);
}
x_703 = l_Lean_indentExpr(x_675);
x_704 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_702)) {
 x_705 = lean_alloc_ctor(7, 2, 0);
} else {
 x_705 = x_702;
 lean_ctor_set_tag(x_705, 7);
}
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
x_706 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_707 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
x_708 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_692, x_707, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_701);
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
x_711 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_683, x_673, x_619, x_618, x_41, x_605, x_617, x_709, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_710);
lean_dec(x_709);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_20 = x_712;
x_21 = x_713;
goto block_28;
}
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_714 = lean_ctor_get(x_684, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_684, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_716 = x_684;
} else {
 lean_dec_ref(x_684);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_714);
lean_ctor_set(x_717, 1, x_715);
return x_717;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_675);
x_718 = lean_ctor_get(x_679, 1);
lean_inc(x_718);
lean_dec(x_679);
lean_inc(x_4);
x_719 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_41, x_605, x_617, x_4, x_618, x_673, x_619, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_718);
lean_dec(x_619);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_20 = x_720;
x_21 = x_721;
goto block_28;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_722 = lean_ctor_get(x_679, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_679, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_724 = x_679;
} else {
 lean_dec_ref(x_679);
 x_724 = lean_box(0);
}
if (lean_is_scalar(x_724)) {
 x_725 = lean_alloc_ctor(1, 2, 0);
} else {
 x_725 = x_724;
}
lean_ctor_set(x_725, 0, x_722);
lean_ctor_set(x_725, 1, x_723);
return x_725;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_41);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_726 = lean_ctor_get(x_676, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_676, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_728 = x_676;
} else {
 lean_dec_ref(x_676);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
}
default: 
{
lean_object* x_730; lean_object* x_731; 
lean_dec(x_620);
lean_dec(x_615);
lean_dec(x_19);
x_730 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_731 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_730, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec(x_731);
if (lean_is_scalar(x_591)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_591;
}
lean_ctor_set(x_733, 0, x_589);
lean_ctor_set(x_733, 1, x_619);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_618);
lean_ctor_set(x_734, 1, x_733);
lean_ctor_set(x_31, 1, x_734);
lean_ctor_set(x_30, 0, x_605);
lean_ctor_set(x_29, 0, x_617);
lean_inc(x_4);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_4);
lean_ctor_set(x_735, 1, x_29);
x_736 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_736, 0, x_735);
x_20 = x_736;
x_21 = x_732;
goto block_28;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_605);
lean_dec(x_591);
lean_dec(x_589);
lean_free_object(x_31);
lean_dec(x_41);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_737 = lean_ctor_get(x_731, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_731, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_739 = x_731;
} else {
 lean_dec_ref(x_731);
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
}
}
}
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; 
x_741 = lean_ctor_get(x_31, 0);
lean_inc(x_741);
lean_dec(x_31);
x_742 = lean_ctor_get(x_32, 0);
lean_inc(x_742);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_743 = x_32;
} else {
 lean_dec_ref(x_32);
 x_743 = lean_box(0);
}
x_744 = lean_ctor_get(x_33, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_33, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_746 = x_33;
} else {
 lean_dec_ref(x_33);
 x_746 = lean_box(0);
}
x_747 = lean_ctor_get(x_35, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_35, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_35, 2);
lean_inc(x_749);
x_750 = lean_nat_dec_lt(x_748, x_749);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_19);
if (lean_is_scalar(x_746)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_746;
}
lean_ctor_set(x_751, 0, x_744);
lean_ctor_set(x_751, 1, x_745);
if (lean_is_scalar(x_743)) {
 x_752 = lean_alloc_ctor(0, 2, 0);
} else {
 x_752 = x_743;
}
lean_ctor_set(x_752, 0, x_742);
lean_ctor_set(x_752, 1, x_751);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_741);
lean_ctor_set(x_753, 1, x_752);
lean_ctor_set(x_30, 1, x_753);
lean_inc(x_4);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_4);
lean_ctor_set(x_754, 1, x_29);
x_755 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_755, 0, x_754);
x_20 = x_755;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_756; lean_object* x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_756 = x_35;
} else {
 lean_dec_ref(x_35);
 x_756 = lean_box(0);
}
x_757 = lean_array_fget(x_747, x_748);
x_758 = lean_unbox(x_757);
lean_dec(x_757);
x_759 = lean_unsigned_to_nat(1u);
x_760 = lean_nat_add(x_748, x_759);
lean_dec(x_748);
if (lean_is_scalar(x_756)) {
 x_761 = lean_alloc_ctor(0, 3, 0);
} else {
 x_761 = x_756;
}
lean_ctor_set(x_761, 0, x_747);
lean_ctor_set(x_761, 1, x_760);
lean_ctor_set(x_761, 2, x_749);
x_762 = lean_ctor_get(x_38, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_38, 1);
lean_inc(x_763);
x_764 = lean_ctor_get(x_38, 2);
lean_inc(x_764);
x_765 = lean_nat_dec_lt(x_763, x_764);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_764);
lean_dec(x_763);
lean_dec(x_762);
lean_dec(x_19);
if (lean_is_scalar(x_746)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_746;
}
lean_ctor_set(x_766, 0, x_744);
lean_ctor_set(x_766, 1, x_745);
if (lean_is_scalar(x_743)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_743;
}
lean_ctor_set(x_767, 0, x_742);
lean_ctor_set(x_767, 1, x_766);
x_768 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_768, 0, x_741);
lean_ctor_set(x_768, 1, x_767);
lean_ctor_set(x_30, 1, x_768);
lean_ctor_set(x_30, 0, x_761);
lean_inc(x_4);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_4);
lean_ctor_set(x_769, 1, x_29);
x_770 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_770, 0, x_769);
x_20 = x_770;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_771 = x_38;
} else {
 lean_dec_ref(x_38);
 x_771 = lean_box(0);
}
x_772 = lean_array_fget(x_762, x_763);
x_773 = lean_nat_add(x_763, x_759);
lean_dec(x_763);
if (lean_is_scalar(x_771)) {
 x_774 = lean_alloc_ctor(0, 3, 0);
} else {
 x_774 = x_771;
}
lean_ctor_set(x_774, 0, x_762);
lean_ctor_set(x_774, 1, x_773);
lean_ctor_set(x_774, 2, x_764);
lean_inc(x_19);
x_775 = l_Lean_Expr_app___override(x_742, x_19);
x_776 = l_Lean_Expr_bindingBody_x21(x_745);
lean_dec(x_745);
x_777 = lean_box(x_758);
switch (lean_obj_tag(x_777)) {
case 0:
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_19);
x_778 = lean_array_push(x_744, x_772);
if (lean_is_scalar(x_746)) {
 x_779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_779 = x_746;
}
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set(x_779, 1, x_776);
if (lean_is_scalar(x_743)) {
 x_780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_780 = x_743;
}
lean_ctor_set(x_780, 0, x_775);
lean_ctor_set(x_780, 1, x_779);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_741);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_30, 1, x_781);
lean_ctor_set(x_30, 0, x_761);
lean_ctor_set(x_29, 0, x_774);
lean_inc(x_4);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_4);
lean_ctor_set(x_782, 1, x_29);
x_783 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_783, 0, x_782);
x_20 = x_783;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_784; lean_object* x_785; uint8_t x_786; 
lean_dec(x_772);
lean_inc(x_19);
x_784 = lean_array_push(x_744, x_19);
x_785 = lean_array_get_size(x_3);
x_786 = lean_nat_dec_lt(x_741, x_785);
lean_dec(x_785);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = l_Lean_Meta_Simp_instInhabitedResult;
x_788 = l_outOfBounds___rarg(x_787);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_788);
x_789 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_788, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_nat_add(x_741, x_759);
lean_dec(x_741);
x_793 = lean_ctor_get(x_788, 0);
lean_inc(x_793);
lean_dec(x_788);
lean_inc(x_790);
lean_inc(x_793);
x_794 = l_Lean_mkAppB(x_775, x_793, x_790);
x_795 = lean_array_push(x_784, x_793);
x_796 = lean_array_push(x_795, x_790);
x_797 = l_Lean_Expr_bindingBody_x21(x_776);
lean_dec(x_776);
x_798 = l_Lean_Expr_bindingBody_x21(x_797);
lean_dec(x_797);
if (lean_is_scalar(x_746)) {
 x_799 = lean_alloc_ctor(0, 2, 0);
} else {
 x_799 = x_746;
}
lean_ctor_set(x_799, 0, x_796);
lean_ctor_set(x_799, 1, x_798);
if (lean_is_scalar(x_743)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_743;
}
lean_ctor_set(x_800, 0, x_794);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_792);
lean_ctor_set(x_801, 1, x_800);
lean_ctor_set(x_30, 1, x_801);
lean_ctor_set(x_30, 0, x_761);
lean_ctor_set(x_29, 0, x_774);
lean_inc(x_4);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_4);
lean_ctor_set(x_802, 1, x_29);
x_803 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_803, 0, x_802);
x_20 = x_803;
x_21 = x_791;
goto block_28;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_788);
lean_dec(x_784);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_746);
lean_dec(x_743);
lean_dec(x_741);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_804 = lean_ctor_get(x_789, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_789, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_806 = x_789;
} else {
 lean_dec_ref(x_789);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_804);
lean_ctor_set(x_807, 1, x_805);
return x_807;
}
}
else
{
lean_object* x_808; lean_object* x_809; 
x_808 = lean_array_fget(x_3, x_741);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_808);
x_809 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_808, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
x_812 = lean_nat_add(x_741, x_759);
lean_dec(x_741);
x_813 = lean_ctor_get(x_808, 0);
lean_inc(x_813);
lean_dec(x_808);
lean_inc(x_810);
lean_inc(x_813);
x_814 = l_Lean_mkAppB(x_775, x_813, x_810);
x_815 = lean_array_push(x_784, x_813);
x_816 = lean_array_push(x_815, x_810);
x_817 = l_Lean_Expr_bindingBody_x21(x_776);
lean_dec(x_776);
x_818 = l_Lean_Expr_bindingBody_x21(x_817);
lean_dec(x_817);
if (lean_is_scalar(x_746)) {
 x_819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_819 = x_746;
}
lean_ctor_set(x_819, 0, x_816);
lean_ctor_set(x_819, 1, x_818);
if (lean_is_scalar(x_743)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_743;
}
lean_ctor_set(x_820, 0, x_814);
lean_ctor_set(x_820, 1, x_819);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_812);
lean_ctor_set(x_821, 1, x_820);
lean_ctor_set(x_30, 1, x_821);
lean_ctor_set(x_30, 0, x_761);
lean_ctor_set(x_29, 0, x_774);
lean_inc(x_4);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_4);
lean_ctor_set(x_822, 1, x_29);
x_823 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_823, 0, x_822);
x_20 = x_823;
x_21 = x_811;
goto block_28;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_808);
lean_dec(x_784);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_746);
lean_dec(x_743);
lean_dec(x_741);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_824 = lean_ctor_get(x_809, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_809, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_826 = x_809;
} else {
 lean_dec_ref(x_809);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
}
case 3:
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_772);
x_828 = lean_array_push(x_744, x_19);
if (lean_is_scalar(x_746)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_746;
}
lean_ctor_set(x_829, 0, x_828);
lean_ctor_set(x_829, 1, x_776);
if (lean_is_scalar(x_743)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_743;
}
lean_ctor_set(x_830, 0, x_775);
lean_ctor_set(x_830, 1, x_829);
x_831 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_831, 0, x_741);
lean_ctor_set(x_831, 1, x_830);
lean_ctor_set(x_30, 1, x_831);
lean_ctor_set(x_30, 0, x_761);
lean_ctor_set(x_29, 0, x_774);
lean_inc(x_4);
x_832 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_832, 0, x_4);
lean_ctor_set(x_832, 1, x_29);
x_833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_833, 0, x_832);
x_20 = x_833;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_772);
lean_dec(x_746);
lean_dec(x_743);
lean_free_object(x_29);
lean_free_object(x_30);
lean_inc(x_19);
x_834 = lean_array_push(x_744, x_19);
x_835 = l_Lean_Expr_bindingDomain_x21(x_776);
x_836 = lean_expr_instantiate_rev(x_835, x_834);
lean_dec(x_835);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_837 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
lean_dec(x_837);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_836);
x_840 = l_Lean_Meta_isExprDefEq(x_838, x_836, x_12, x_13, x_14, x_15, x_839);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; uint8_t x_842; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_unbox(x_841);
lean_dec(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
lean_dec(x_19);
x_843 = lean_ctor_get(x_840, 1);
lean_inc(x_843);
lean_dec(x_840);
x_844 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_836);
x_845 = l_Lean_Meta_trySynthInstance(x_836, x_844, x_12, x_13, x_14, x_15, x_843);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
if (lean_obj_tag(x_846) == 1)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_836);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
lean_dec(x_846);
lean_inc(x_4);
x_849 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_741, x_761, x_774, x_4, x_775, x_834, x_776, x_848, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_847);
lean_dec(x_776);
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec(x_849);
x_20 = x_850;
x_21 = x_851;
goto block_28;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; 
lean_dec(x_846);
x_852 = lean_ctor_get(x_845, 1);
lean_inc(x_852);
lean_dec(x_845);
x_853 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_854 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_853, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_852);
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_unbox(x_855);
lean_dec(x_855);
if (x_856 == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_dec(x_836);
x_857 = lean_ctor_get(x_854, 1);
lean_inc(x_857);
lean_dec(x_854);
x_858 = lean_box(0);
x_859 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_844, x_834, x_776, x_775, x_741, x_761, x_774, x_858, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_857);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
x_20 = x_860;
x_21 = x_861;
goto block_28;
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_862 = lean_ctor_get(x_854, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_863 = x_854;
} else {
 lean_dec_ref(x_854);
 x_863 = lean_box(0);
}
x_864 = l_Lean_indentExpr(x_836);
x_865 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_863)) {
 x_866 = lean_alloc_ctor(7, 2, 0);
} else {
 x_866 = x_863;
 lean_ctor_set_tag(x_866, 7);
}
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_864);
x_867 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_868 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_868, 0, x_866);
lean_ctor_set(x_868, 1, x_867);
x_869 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_853, x_868, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_862);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_844, x_834, x_776, x_775, x_741, x_761, x_774, x_870, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_871);
lean_dec(x_870);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_20 = x_873;
x_21 = x_874;
goto block_28;
}
}
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_836);
lean_dec(x_834);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_741);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_875 = lean_ctor_get(x_845, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_845, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_877 = x_845;
} else {
 lean_dec_ref(x_845);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_875);
lean_ctor_set(x_878, 1, x_876);
return x_878;
}
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_836);
x_879 = lean_ctor_get(x_840, 1);
lean_inc(x_879);
lean_dec(x_840);
lean_inc(x_4);
x_880 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_741, x_761, x_774, x_4, x_775, x_834, x_776, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_879);
lean_dec(x_776);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
x_20 = x_881;
x_21 = x_882;
goto block_28;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_836);
lean_dec(x_834);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_741);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_883 = lean_ctor_get(x_840, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_840, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_885 = x_840;
} else {
 lean_dec_ref(x_840);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_836);
lean_dec(x_834);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_741);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_887 = lean_ctor_get(x_837, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_837, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_889 = x_837;
} else {
 lean_dec_ref(x_837);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
default: 
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_777);
lean_dec(x_772);
lean_dec(x_19);
x_891 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_892 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_891, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec(x_892);
if (lean_is_scalar(x_746)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_746;
}
lean_ctor_set(x_894, 0, x_744);
lean_ctor_set(x_894, 1, x_776);
if (lean_is_scalar(x_743)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_743;
}
lean_ctor_set(x_895, 0, x_775);
lean_ctor_set(x_895, 1, x_894);
x_896 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_896, 0, x_741);
lean_ctor_set(x_896, 1, x_895);
lean_ctor_set(x_30, 1, x_896);
lean_ctor_set(x_30, 0, x_761);
lean_ctor_set(x_29, 0, x_774);
lean_inc(x_4);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_4);
lean_ctor_set(x_897, 1, x_29);
x_898 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_898, 0, x_897);
x_20 = x_898;
x_21 = x_893;
goto block_28;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_761);
lean_dec(x_746);
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_741);
lean_free_object(x_29);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_899 = lean_ctor_get(x_892, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_892, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 x_901 = x_892;
} else {
 lean_dec_ref(x_892);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
}
}
}
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; uint8_t x_914; 
x_903 = lean_ctor_get(x_29, 0);
lean_inc(x_903);
lean_dec(x_29);
x_904 = lean_ctor_get(x_31, 0);
lean_inc(x_904);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_905 = x_31;
} else {
 lean_dec_ref(x_31);
 x_905 = lean_box(0);
}
x_906 = lean_ctor_get(x_32, 0);
lean_inc(x_906);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_907 = x_32;
} else {
 lean_dec_ref(x_32);
 x_907 = lean_box(0);
}
x_908 = lean_ctor_get(x_33, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_33, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_910 = x_33;
} else {
 lean_dec_ref(x_33);
 x_910 = lean_box(0);
}
x_911 = lean_ctor_get(x_35, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_35, 1);
lean_inc(x_912);
x_913 = lean_ctor_get(x_35, 2);
lean_inc(x_913);
x_914 = lean_nat_dec_lt(x_912, x_913);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_913);
lean_dec(x_912);
lean_dec(x_911);
lean_dec(x_19);
if (lean_is_scalar(x_910)) {
 x_915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_915 = x_910;
}
lean_ctor_set(x_915, 0, x_908);
lean_ctor_set(x_915, 1, x_909);
if (lean_is_scalar(x_907)) {
 x_916 = lean_alloc_ctor(0, 2, 0);
} else {
 x_916 = x_907;
}
lean_ctor_set(x_916, 0, x_906);
lean_ctor_set(x_916, 1, x_915);
if (lean_is_scalar(x_905)) {
 x_917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_917 = x_905;
}
lean_ctor_set(x_917, 0, x_904);
lean_ctor_set(x_917, 1, x_916);
lean_ctor_set(x_30, 1, x_917);
x_918 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_918, 0, x_903);
lean_ctor_set(x_918, 1, x_30);
lean_inc(x_4);
x_919 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_919, 0, x_4);
lean_ctor_set(x_919, 1, x_918);
x_920 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_920, 0, x_919);
x_20 = x_920;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_921; lean_object* x_922; uint8_t x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; uint8_t x_930; 
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_921 = x_35;
} else {
 lean_dec_ref(x_35);
 x_921 = lean_box(0);
}
x_922 = lean_array_fget(x_911, x_912);
x_923 = lean_unbox(x_922);
lean_dec(x_922);
x_924 = lean_unsigned_to_nat(1u);
x_925 = lean_nat_add(x_912, x_924);
lean_dec(x_912);
if (lean_is_scalar(x_921)) {
 x_926 = lean_alloc_ctor(0, 3, 0);
} else {
 x_926 = x_921;
}
lean_ctor_set(x_926, 0, x_911);
lean_ctor_set(x_926, 1, x_925);
lean_ctor_set(x_926, 2, x_913);
x_927 = lean_ctor_get(x_903, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_903, 1);
lean_inc(x_928);
x_929 = lean_ctor_get(x_903, 2);
lean_inc(x_929);
x_930 = lean_nat_dec_lt(x_928, x_929);
if (x_930 == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_dec(x_929);
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_19);
if (lean_is_scalar(x_910)) {
 x_931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_931 = x_910;
}
lean_ctor_set(x_931, 0, x_908);
lean_ctor_set(x_931, 1, x_909);
if (lean_is_scalar(x_907)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_907;
}
lean_ctor_set(x_932, 0, x_906);
lean_ctor_set(x_932, 1, x_931);
if (lean_is_scalar(x_905)) {
 x_933 = lean_alloc_ctor(0, 2, 0);
} else {
 x_933 = x_905;
}
lean_ctor_set(x_933, 0, x_904);
lean_ctor_set(x_933, 1, x_932);
lean_ctor_set(x_30, 1, x_933);
lean_ctor_set(x_30, 0, x_926);
x_934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_934, 0, x_903);
lean_ctor_set(x_934, 1, x_30);
lean_inc(x_4);
x_935 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_935, 0, x_4);
lean_ctor_set(x_935, 1, x_934);
x_936 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_936, 0, x_935);
x_20 = x_936;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 lean_ctor_release(x_903, 2);
 x_937 = x_903;
} else {
 lean_dec_ref(x_903);
 x_937 = lean_box(0);
}
x_938 = lean_array_fget(x_927, x_928);
x_939 = lean_nat_add(x_928, x_924);
lean_dec(x_928);
if (lean_is_scalar(x_937)) {
 x_940 = lean_alloc_ctor(0, 3, 0);
} else {
 x_940 = x_937;
}
lean_ctor_set(x_940, 0, x_927);
lean_ctor_set(x_940, 1, x_939);
lean_ctor_set(x_940, 2, x_929);
lean_inc(x_19);
x_941 = l_Lean_Expr_app___override(x_906, x_19);
x_942 = l_Lean_Expr_bindingBody_x21(x_909);
lean_dec(x_909);
x_943 = lean_box(x_923);
switch (lean_obj_tag(x_943)) {
case 0:
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_19);
x_944 = lean_array_push(x_908, x_938);
if (lean_is_scalar(x_910)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_910;
}
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_945, 1, x_942);
if (lean_is_scalar(x_907)) {
 x_946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_946 = x_907;
}
lean_ctor_set(x_946, 0, x_941);
lean_ctor_set(x_946, 1, x_945);
if (lean_is_scalar(x_905)) {
 x_947 = lean_alloc_ctor(0, 2, 0);
} else {
 x_947 = x_905;
}
lean_ctor_set(x_947, 0, x_904);
lean_ctor_set(x_947, 1, x_946);
lean_ctor_set(x_30, 1, x_947);
lean_ctor_set(x_30, 0, x_926);
x_948 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_948, 0, x_940);
lean_ctor_set(x_948, 1, x_30);
lean_inc(x_4);
x_949 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_949, 0, x_4);
lean_ctor_set(x_949, 1, x_948);
x_950 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_950, 0, x_949);
x_20 = x_950;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_951; lean_object* x_952; uint8_t x_953; 
lean_dec(x_938);
lean_inc(x_19);
x_951 = lean_array_push(x_908, x_19);
x_952 = lean_array_get_size(x_3);
x_953 = lean_nat_dec_lt(x_904, x_952);
lean_dec(x_952);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_954 = l_Lean_Meta_Simp_instInhabitedResult;
x_955 = l_outOfBounds___rarg(x_954);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_955);
x_956 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_955, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
x_959 = lean_nat_add(x_904, x_924);
lean_dec(x_904);
x_960 = lean_ctor_get(x_955, 0);
lean_inc(x_960);
lean_dec(x_955);
lean_inc(x_957);
lean_inc(x_960);
x_961 = l_Lean_mkAppB(x_941, x_960, x_957);
x_962 = lean_array_push(x_951, x_960);
x_963 = lean_array_push(x_962, x_957);
x_964 = l_Lean_Expr_bindingBody_x21(x_942);
lean_dec(x_942);
x_965 = l_Lean_Expr_bindingBody_x21(x_964);
lean_dec(x_964);
if (lean_is_scalar(x_910)) {
 x_966 = lean_alloc_ctor(0, 2, 0);
} else {
 x_966 = x_910;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_965);
if (lean_is_scalar(x_907)) {
 x_967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_967 = x_907;
}
lean_ctor_set(x_967, 0, x_961);
lean_ctor_set(x_967, 1, x_966);
if (lean_is_scalar(x_905)) {
 x_968 = lean_alloc_ctor(0, 2, 0);
} else {
 x_968 = x_905;
}
lean_ctor_set(x_968, 0, x_959);
lean_ctor_set(x_968, 1, x_967);
lean_ctor_set(x_30, 1, x_968);
lean_ctor_set(x_30, 0, x_926);
x_969 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_969, 0, x_940);
lean_ctor_set(x_969, 1, x_30);
lean_inc(x_4);
x_970 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_970, 0, x_4);
lean_ctor_set(x_970, 1, x_969);
x_971 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_971, 0, x_970);
x_20 = x_971;
x_21 = x_958;
goto block_28;
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_955);
lean_dec(x_951);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_910);
lean_dec(x_907);
lean_dec(x_905);
lean_dec(x_904);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_972 = lean_ctor_get(x_956, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_956, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_974 = x_956;
} else {
 lean_dec_ref(x_956);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_972);
lean_ctor_set(x_975, 1, x_973);
return x_975;
}
}
else
{
lean_object* x_976; lean_object* x_977; 
x_976 = lean_array_fget(x_3, x_904);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_976);
x_977 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_976, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec(x_977);
x_980 = lean_nat_add(x_904, x_924);
lean_dec(x_904);
x_981 = lean_ctor_get(x_976, 0);
lean_inc(x_981);
lean_dec(x_976);
lean_inc(x_978);
lean_inc(x_981);
x_982 = l_Lean_mkAppB(x_941, x_981, x_978);
x_983 = lean_array_push(x_951, x_981);
x_984 = lean_array_push(x_983, x_978);
x_985 = l_Lean_Expr_bindingBody_x21(x_942);
lean_dec(x_942);
x_986 = l_Lean_Expr_bindingBody_x21(x_985);
lean_dec(x_985);
if (lean_is_scalar(x_910)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_910;
}
lean_ctor_set(x_987, 0, x_984);
lean_ctor_set(x_987, 1, x_986);
if (lean_is_scalar(x_907)) {
 x_988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_988 = x_907;
}
lean_ctor_set(x_988, 0, x_982);
lean_ctor_set(x_988, 1, x_987);
if (lean_is_scalar(x_905)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_905;
}
lean_ctor_set(x_989, 0, x_980);
lean_ctor_set(x_989, 1, x_988);
lean_ctor_set(x_30, 1, x_989);
lean_ctor_set(x_30, 0, x_926);
x_990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_990, 0, x_940);
lean_ctor_set(x_990, 1, x_30);
lean_inc(x_4);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_4);
lean_ctor_set(x_991, 1, x_990);
x_992 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_992, 0, x_991);
x_20 = x_992;
x_21 = x_979;
goto block_28;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_976);
lean_dec(x_951);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_910);
lean_dec(x_907);
lean_dec(x_905);
lean_dec(x_904);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_993 = lean_ctor_get(x_977, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_977, 1);
lean_inc(x_994);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_995 = x_977;
} else {
 lean_dec_ref(x_977);
 x_995 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_996 = lean_alloc_ctor(1, 2, 0);
} else {
 x_996 = x_995;
}
lean_ctor_set(x_996, 0, x_993);
lean_ctor_set(x_996, 1, x_994);
return x_996;
}
}
}
case 3:
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_938);
x_997 = lean_array_push(x_908, x_19);
if (lean_is_scalar(x_910)) {
 x_998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_998 = x_910;
}
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_942);
if (lean_is_scalar(x_907)) {
 x_999 = lean_alloc_ctor(0, 2, 0);
} else {
 x_999 = x_907;
}
lean_ctor_set(x_999, 0, x_941);
lean_ctor_set(x_999, 1, x_998);
if (lean_is_scalar(x_905)) {
 x_1000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1000 = x_905;
}
lean_ctor_set(x_1000, 0, x_904);
lean_ctor_set(x_1000, 1, x_999);
lean_ctor_set(x_30, 1, x_1000);
lean_ctor_set(x_30, 0, x_926);
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_940);
lean_ctor_set(x_1001, 1, x_30);
lean_inc(x_4);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_4);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
x_20 = x_1003;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_938);
lean_dec(x_910);
lean_dec(x_907);
lean_dec(x_905);
lean_free_object(x_30);
lean_inc(x_19);
x_1004 = lean_array_push(x_908, x_19);
x_1005 = l_Lean_Expr_bindingDomain_x21(x_942);
x_1006 = lean_expr_instantiate_rev(x_1005, x_1004);
lean_dec(x_1005);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_1007 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
lean_dec(x_1007);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1006);
x_1010 = l_Lean_Meta_isExprDefEq(x_1008, x_1006, x_12, x_13, x_14, x_15, x_1009);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; uint8_t x_1012; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_unbox(x_1011);
lean_dec(x_1011);
if (x_1012 == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
lean_dec(x_19);
x_1013 = lean_ctor_get(x_1010, 1);
lean_inc(x_1013);
lean_dec(x_1010);
x_1014 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1006);
x_1015 = l_Lean_Meta_trySynthInstance(x_1006, x_1014, x_12, x_13, x_14, x_15, x_1013);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
if (lean_obj_tag(x_1016) == 1)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_1006);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
x_1018 = lean_ctor_get(x_1016, 0);
lean_inc(x_1018);
lean_dec(x_1016);
lean_inc(x_4);
x_1019 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_904, x_926, x_940, x_4, x_941, x_1004, x_942, x_1018, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1017);
lean_dec(x_942);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_20 = x_1020;
x_21 = x_1021;
goto block_28;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
lean_dec(x_1016);
x_1022 = lean_ctor_get(x_1015, 1);
lean_inc(x_1022);
lean_dec(x_1015);
x_1023 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_1024 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1023, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1022);
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc(x_1025);
x_1026 = lean_unbox(x_1025);
lean_dec(x_1025);
if (x_1026 == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_1006);
x_1027 = lean_ctor_get(x_1024, 1);
lean_inc(x_1027);
lean_dec(x_1024);
x_1028 = lean_box(0);
x_1029 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1014, x_1004, x_942, x_941, x_904, x_926, x_940, x_1028, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1027);
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_20 = x_1030;
x_21 = x_1031;
goto block_28;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1032 = lean_ctor_get(x_1024, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 lean_ctor_release(x_1024, 1);
 x_1033 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1033 = lean_box(0);
}
x_1034 = l_Lean_indentExpr(x_1006);
x_1035 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_1033)) {
 x_1036 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1036 = x_1033;
 lean_ctor_set_tag(x_1036, 7);
}
lean_ctor_set(x_1036, 0, x_1035);
lean_ctor_set(x_1036, 1, x_1034);
x_1037 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_1038 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
x_1039 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_1023, x_1038, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1032);
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec(x_1039);
x_1042 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1014, x_1004, x_942, x_941, x_904, x_926, x_940, x_1040, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1041);
lean_dec(x_1040);
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
lean_dec(x_1042);
x_20 = x_1043;
x_21 = x_1044;
goto block_28;
}
}
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_904);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1045 = lean_ctor_get(x_1015, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1015, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1047 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1045);
lean_ctor_set(x_1048, 1, x_1046);
return x_1048;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1006);
x_1049 = lean_ctor_get(x_1010, 1);
lean_inc(x_1049);
lean_dec(x_1010);
lean_inc(x_4);
x_1050 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_904, x_926, x_940, x_4, x_941, x_1004, x_942, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1049);
lean_dec(x_942);
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1050, 1);
lean_inc(x_1052);
lean_dec(x_1050);
x_20 = x_1051;
x_21 = x_1052;
goto block_28;
}
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_904);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1053 = lean_ctor_get(x_1010, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1010, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1055 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1053);
lean_ctor_set(x_1056, 1, x_1054);
return x_1056;
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1006);
lean_dec(x_1004);
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_904);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1057 = lean_ctor_get(x_1007, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1007, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1059 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_1057);
lean_ctor_set(x_1060, 1, x_1058);
return x_1060;
}
}
default: 
{
lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_943);
lean_dec(x_938);
lean_dec(x_19);
x_1061 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1062 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_1061, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1063 = lean_ctor_get(x_1062, 1);
lean_inc(x_1063);
lean_dec(x_1062);
if (lean_is_scalar(x_910)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_910;
}
lean_ctor_set(x_1064, 0, x_908);
lean_ctor_set(x_1064, 1, x_942);
if (lean_is_scalar(x_907)) {
 x_1065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1065 = x_907;
}
lean_ctor_set(x_1065, 0, x_941);
lean_ctor_set(x_1065, 1, x_1064);
if (lean_is_scalar(x_905)) {
 x_1066 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1066 = x_905;
}
lean_ctor_set(x_1066, 0, x_904);
lean_ctor_set(x_1066, 1, x_1065);
lean_ctor_set(x_30, 1, x_1066);
lean_ctor_set(x_30, 0, x_926);
x_1067 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1067, 0, x_940);
lean_ctor_set(x_1067, 1, x_30);
lean_inc(x_4);
x_1068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1068, 0, x_4);
lean_ctor_set(x_1068, 1, x_1067);
x_1069 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1069, 0, x_1068);
x_20 = x_1069;
x_21 = x_1063;
goto block_28;
}
else
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_942);
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_926);
lean_dec(x_910);
lean_dec(x_908);
lean_dec(x_907);
lean_dec(x_905);
lean_dec(x_904);
lean_free_object(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1070 = lean_ctor_get(x_1062, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1062, 1);
lean_inc(x_1071);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1072 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1070);
lean_ctor_set(x_1073, 1, x_1071);
return x_1073;
}
}
}
}
}
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; 
x_1074 = lean_ctor_get(x_30, 0);
lean_inc(x_1074);
lean_dec(x_30);
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
x_1077 = lean_ctor_get(x_31, 0);
lean_inc(x_1077);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_1078 = x_31;
} else {
 lean_dec_ref(x_31);
 x_1078 = lean_box(0);
}
x_1079 = lean_ctor_get(x_32, 0);
lean_inc(x_1079);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_1080 = x_32;
} else {
 lean_dec_ref(x_32);
 x_1080 = lean_box(0);
}
x_1081 = lean_ctor_get(x_33, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_33, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_1083 = x_33;
} else {
 lean_dec_ref(x_33);
 x_1083 = lean_box(0);
}
x_1084 = lean_ctor_get(x_1074, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1074, 1);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1074, 2);
lean_inc(x_1086);
x_1087 = lean_nat_dec_lt(x_1085, x_1086);
if (x_1087 == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1086);
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_19);
if (lean_is_scalar(x_1083)) {
 x_1088 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1088 = x_1083;
}
lean_ctor_set(x_1088, 0, x_1081);
lean_ctor_set(x_1088, 1, x_1082);
if (lean_is_scalar(x_1080)) {
 x_1089 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1089 = x_1080;
}
lean_ctor_set(x_1089, 0, x_1079);
lean_ctor_set(x_1089, 1, x_1088);
if (lean_is_scalar(x_1078)) {
 x_1090 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1090 = x_1078;
}
lean_ctor_set(x_1090, 0, x_1077);
lean_ctor_set(x_1090, 1, x_1089);
x_1091 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1091, 0, x_1074);
lean_ctor_set(x_1091, 1, x_1090);
if (lean_is_scalar(x_1076)) {
 x_1092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1092 = x_1076;
}
lean_ctor_set(x_1092, 0, x_1075);
lean_ctor_set(x_1092, 1, x_1091);
lean_inc(x_4);
x_1093 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1093, 0, x_4);
lean_ctor_set(x_1093, 1, x_1092);
x_1094 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1094, 0, x_1093);
x_20 = x_1094;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; 
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 lean_ctor_release(x_1074, 2);
 x_1095 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1095 = lean_box(0);
}
x_1096 = lean_array_fget(x_1084, x_1085);
x_1097 = lean_unbox(x_1096);
lean_dec(x_1096);
x_1098 = lean_unsigned_to_nat(1u);
x_1099 = lean_nat_add(x_1085, x_1098);
lean_dec(x_1085);
if (lean_is_scalar(x_1095)) {
 x_1100 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1100 = x_1095;
}
lean_ctor_set(x_1100, 0, x_1084);
lean_ctor_set(x_1100, 1, x_1099);
lean_ctor_set(x_1100, 2, x_1086);
x_1101 = lean_ctor_get(x_1075, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1075, 1);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1075, 2);
lean_inc(x_1103);
x_1104 = lean_nat_dec_lt(x_1102, x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1103);
lean_dec(x_1102);
lean_dec(x_1101);
lean_dec(x_19);
if (lean_is_scalar(x_1083)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1083;
}
lean_ctor_set(x_1105, 0, x_1081);
lean_ctor_set(x_1105, 1, x_1082);
if (lean_is_scalar(x_1080)) {
 x_1106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1106 = x_1080;
}
lean_ctor_set(x_1106, 0, x_1079);
lean_ctor_set(x_1106, 1, x_1105);
if (lean_is_scalar(x_1078)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_1078;
}
lean_ctor_set(x_1107, 0, x_1077);
lean_ctor_set(x_1107, 1, x_1106);
x_1108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1108, 0, x_1100);
lean_ctor_set(x_1108, 1, x_1107);
if (lean_is_scalar(x_1076)) {
 x_1109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1109 = x_1076;
}
lean_ctor_set(x_1109, 0, x_1075);
lean_ctor_set(x_1109, 1, x_1108);
lean_inc(x_4);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_4);
lean_ctor_set(x_1110, 1, x_1109);
x_1111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1111, 0, x_1110);
x_20 = x_1111;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 lean_ctor_release(x_1075, 2);
 x_1112 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1112 = lean_box(0);
}
x_1113 = lean_array_fget(x_1101, x_1102);
x_1114 = lean_nat_add(x_1102, x_1098);
lean_dec(x_1102);
if (lean_is_scalar(x_1112)) {
 x_1115 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1115 = x_1112;
}
lean_ctor_set(x_1115, 0, x_1101);
lean_ctor_set(x_1115, 1, x_1114);
lean_ctor_set(x_1115, 2, x_1103);
lean_inc(x_19);
x_1116 = l_Lean_Expr_app___override(x_1079, x_19);
x_1117 = l_Lean_Expr_bindingBody_x21(x_1082);
lean_dec(x_1082);
x_1118 = lean_box(x_1097);
switch (lean_obj_tag(x_1118)) {
case 0:
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_19);
x_1119 = lean_array_push(x_1081, x_1113);
if (lean_is_scalar(x_1083)) {
 x_1120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1120 = x_1083;
}
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_1117);
if (lean_is_scalar(x_1080)) {
 x_1121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1121 = x_1080;
}
lean_ctor_set(x_1121, 0, x_1116);
lean_ctor_set(x_1121, 1, x_1120);
if (lean_is_scalar(x_1078)) {
 x_1122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1122 = x_1078;
}
lean_ctor_set(x_1122, 0, x_1077);
lean_ctor_set(x_1122, 1, x_1121);
x_1123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1123, 0, x_1100);
lean_ctor_set(x_1123, 1, x_1122);
if (lean_is_scalar(x_1076)) {
 x_1124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1124 = x_1076;
}
lean_ctor_set(x_1124, 0, x_1115);
lean_ctor_set(x_1124, 1, x_1123);
lean_inc(x_4);
x_1125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1125, 0, x_4);
lean_ctor_set(x_1125, 1, x_1124);
x_1126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1126, 0, x_1125);
x_20 = x_1126;
x_21 = x_16;
goto block_28;
}
case 2:
{
lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; 
lean_dec(x_1113);
lean_inc(x_19);
x_1127 = lean_array_push(x_1081, x_19);
x_1128 = lean_array_get_size(x_3);
x_1129 = lean_nat_dec_lt(x_1077, x_1128);
lean_dec(x_1128);
if (x_1129 == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = l_Lean_Meta_Simp_instInhabitedResult;
x_1131 = l_outOfBounds___rarg(x_1130);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1131);
x_1132 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_1131, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1132) == 0)
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1132, 1);
lean_inc(x_1134);
lean_dec(x_1132);
x_1135 = lean_nat_add(x_1077, x_1098);
lean_dec(x_1077);
x_1136 = lean_ctor_get(x_1131, 0);
lean_inc(x_1136);
lean_dec(x_1131);
lean_inc(x_1133);
lean_inc(x_1136);
x_1137 = l_Lean_mkAppB(x_1116, x_1136, x_1133);
x_1138 = lean_array_push(x_1127, x_1136);
x_1139 = lean_array_push(x_1138, x_1133);
x_1140 = l_Lean_Expr_bindingBody_x21(x_1117);
lean_dec(x_1117);
x_1141 = l_Lean_Expr_bindingBody_x21(x_1140);
lean_dec(x_1140);
if (lean_is_scalar(x_1083)) {
 x_1142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1142 = x_1083;
}
lean_ctor_set(x_1142, 0, x_1139);
lean_ctor_set(x_1142, 1, x_1141);
if (lean_is_scalar(x_1080)) {
 x_1143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1143 = x_1080;
}
lean_ctor_set(x_1143, 0, x_1137);
lean_ctor_set(x_1143, 1, x_1142);
if (lean_is_scalar(x_1078)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1078;
}
lean_ctor_set(x_1144, 0, x_1135);
lean_ctor_set(x_1144, 1, x_1143);
x_1145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1145, 0, x_1100);
lean_ctor_set(x_1145, 1, x_1144);
if (lean_is_scalar(x_1076)) {
 x_1146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1146 = x_1076;
}
lean_ctor_set(x_1146, 0, x_1115);
lean_ctor_set(x_1146, 1, x_1145);
lean_inc(x_4);
x_1147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1147, 0, x_4);
lean_ctor_set(x_1147, 1, x_1146);
x_1148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1148, 0, x_1147);
x_20 = x_1148;
x_21 = x_1134;
goto block_28;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_1131);
lean_dec(x_1127);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1083);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1076);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1149 = lean_ctor_get(x_1132, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1132, 1);
lean_inc(x_1150);
if (lean_is_exclusive(x_1132)) {
 lean_ctor_release(x_1132, 0);
 lean_ctor_release(x_1132, 1);
 x_1151 = x_1132;
} else {
 lean_dec_ref(x_1132);
 x_1151 = lean_box(0);
}
if (lean_is_scalar(x_1151)) {
 x_1152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1152 = x_1151;
}
lean_ctor_set(x_1152, 0, x_1149);
lean_ctor_set(x_1152, 1, x_1150);
return x_1152;
}
}
else
{
lean_object* x_1153; lean_object* x_1154; 
x_1153 = lean_array_fget(x_3, x_1077);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1153);
x_1154 = l_Lean_Meta_Simp_Result_getProof_x27(x_19, x_1153, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
lean_dec(x_1154);
x_1157 = lean_nat_add(x_1077, x_1098);
lean_dec(x_1077);
x_1158 = lean_ctor_get(x_1153, 0);
lean_inc(x_1158);
lean_dec(x_1153);
lean_inc(x_1155);
lean_inc(x_1158);
x_1159 = l_Lean_mkAppB(x_1116, x_1158, x_1155);
x_1160 = lean_array_push(x_1127, x_1158);
x_1161 = lean_array_push(x_1160, x_1155);
x_1162 = l_Lean_Expr_bindingBody_x21(x_1117);
lean_dec(x_1117);
x_1163 = l_Lean_Expr_bindingBody_x21(x_1162);
lean_dec(x_1162);
if (lean_is_scalar(x_1083)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1083;
}
lean_ctor_set(x_1164, 0, x_1161);
lean_ctor_set(x_1164, 1, x_1163);
if (lean_is_scalar(x_1080)) {
 x_1165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1165 = x_1080;
}
lean_ctor_set(x_1165, 0, x_1159);
lean_ctor_set(x_1165, 1, x_1164);
if (lean_is_scalar(x_1078)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1078;
}
lean_ctor_set(x_1166, 0, x_1157);
lean_ctor_set(x_1166, 1, x_1165);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_1100);
lean_ctor_set(x_1167, 1, x_1166);
if (lean_is_scalar(x_1076)) {
 x_1168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1168 = x_1076;
}
lean_ctor_set(x_1168, 0, x_1115);
lean_ctor_set(x_1168, 1, x_1167);
lean_inc(x_4);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_4);
lean_ctor_set(x_1169, 1, x_1168);
x_1170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1170, 0, x_1169);
x_20 = x_1170;
x_21 = x_1156;
goto block_28;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec(x_1153);
lean_dec(x_1127);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1083);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1076);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1171 = lean_ctor_get(x_1154, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1154, 1);
lean_inc(x_1172);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1173 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1173 = lean_box(0);
}
if (lean_is_scalar(x_1173)) {
 x_1174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1174 = x_1173;
}
lean_ctor_set(x_1174, 0, x_1171);
lean_ctor_set(x_1174, 1, x_1172);
return x_1174;
}
}
}
case 3:
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
lean_dec(x_1113);
x_1175 = lean_array_push(x_1081, x_19);
if (lean_is_scalar(x_1083)) {
 x_1176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1176 = x_1083;
}
lean_ctor_set(x_1176, 0, x_1175);
lean_ctor_set(x_1176, 1, x_1117);
if (lean_is_scalar(x_1080)) {
 x_1177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1177 = x_1080;
}
lean_ctor_set(x_1177, 0, x_1116);
lean_ctor_set(x_1177, 1, x_1176);
if (lean_is_scalar(x_1078)) {
 x_1178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1178 = x_1078;
}
lean_ctor_set(x_1178, 0, x_1077);
lean_ctor_set(x_1178, 1, x_1177);
x_1179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1179, 0, x_1100);
lean_ctor_set(x_1179, 1, x_1178);
if (lean_is_scalar(x_1076)) {
 x_1180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1180 = x_1076;
}
lean_ctor_set(x_1180, 0, x_1115);
lean_ctor_set(x_1180, 1, x_1179);
lean_inc(x_4);
x_1181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1181, 0, x_4);
lean_ctor_set(x_1181, 1, x_1180);
x_1182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1182, 0, x_1181);
x_20 = x_1182;
x_21 = x_16;
goto block_28;
}
case 5:
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
lean_dec(x_1113);
lean_dec(x_1083);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1076);
lean_inc(x_19);
x_1183 = lean_array_push(x_1081, x_19);
x_1184 = l_Lean_Expr_bindingDomain_x21(x_1117);
x_1185 = lean_expr_instantiate_rev(x_1184, x_1183);
lean_dec(x_1184);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_1186 = lean_infer_type(x_19, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1186, 1);
lean_inc(x_1188);
lean_dec(x_1186);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1185);
x_1189 = l_Lean_Meta_isExprDefEq(x_1187, x_1185, x_12, x_13, x_14, x_15, x_1188);
if (lean_obj_tag(x_1189) == 0)
{
lean_object* x_1190; uint8_t x_1191; 
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_unbox(x_1190);
lean_dec(x_1190);
if (x_1191 == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_19);
x_1192 = lean_ctor_get(x_1189, 1);
lean_inc(x_1192);
lean_dec(x_1189);
x_1193 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1185);
x_1194 = l_Lean_Meta_trySynthInstance(x_1185, x_1193, x_12, x_13, x_14, x_15, x_1192);
if (lean_obj_tag(x_1194) == 0)
{
lean_object* x_1195; 
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
if (lean_obj_tag(x_1195) == 1)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1185);
x_1196 = lean_ctor_get(x_1194, 1);
lean_inc(x_1196);
lean_dec(x_1194);
x_1197 = lean_ctor_get(x_1195, 0);
lean_inc(x_1197);
lean_dec(x_1195);
lean_inc(x_4);
x_1198 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1077, x_1100, x_1115, x_4, x_1116, x_1183, x_1117, x_1197, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1196);
lean_dec(x_1117);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_20 = x_1199;
x_21 = x_1200;
goto block_28;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; uint8_t x_1205; 
lean_dec(x_1195);
x_1201 = lean_ctor_get(x_1194, 1);
lean_inc(x_1201);
lean_dec(x_1194);
x_1202 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_1203 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1202, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1201);
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_unbox(x_1204);
lean_dec(x_1204);
if (x_1205 == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
lean_dec(x_1185);
x_1206 = lean_ctor_get(x_1203, 1);
lean_inc(x_1206);
lean_dec(x_1203);
x_1207 = lean_box(0);
x_1208 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1193, x_1183, x_1117, x_1116, x_1077, x_1100, x_1115, x_1207, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1206);
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1208, 1);
lean_inc(x_1210);
lean_dec(x_1208);
x_20 = x_1209;
x_21 = x_1210;
goto block_28;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1211 = lean_ctor_get(x_1203, 1);
lean_inc(x_1211);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 lean_ctor_release(x_1203, 1);
 x_1212 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1212 = lean_box(0);
}
x_1213 = l_Lean_indentExpr(x_1185);
x_1214 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
if (lean_is_scalar(x_1212)) {
 x_1215 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1215 = x_1212;
 lean_ctor_set_tag(x_1215, 7);
}
lean_ctor_set(x_1215, 0, x_1214);
lean_ctor_set(x_1215, 1, x_1213);
x_1216 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_1217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1217, 0, x_1215);
lean_ctor_set(x_1217, 1, x_1216);
x_1218 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_1202, x_1217, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1211);
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1218, 1);
lean_inc(x_1220);
lean_dec(x_1218);
x_1221 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1193, x_1183, x_1117, x_1116, x_1077, x_1100, x_1115, x_1219, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1220);
lean_dec(x_1219);
x_1222 = lean_ctor_get(x_1221, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1221, 1);
lean_inc(x_1223);
lean_dec(x_1221);
x_20 = x_1222;
x_21 = x_1223;
goto block_28;
}
}
}
else
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
lean_dec(x_1185);
lean_dec(x_1183);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1077);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1224 = lean_ctor_get(x_1194, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1194, 1);
lean_inc(x_1225);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 x_1226 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1226 = lean_box(0);
}
if (lean_is_scalar(x_1226)) {
 x_1227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1227 = x_1226;
}
lean_ctor_set(x_1227, 0, x_1224);
lean_ctor_set(x_1227, 1, x_1225);
return x_1227;
}
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
lean_dec(x_1185);
x_1228 = lean_ctor_get(x_1189, 1);
lean_inc(x_1228);
lean_dec(x_1189);
lean_inc(x_4);
x_1229 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1077, x_1100, x_1115, x_4, x_1116, x_1183, x_1117, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1228);
lean_dec(x_1117);
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1229, 1);
lean_inc(x_1231);
lean_dec(x_1229);
x_20 = x_1230;
x_21 = x_1231;
goto block_28;
}
}
else
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1185);
lean_dec(x_1183);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1077);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1232 = lean_ctor_get(x_1189, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1189, 1);
lean_inc(x_1233);
if (lean_is_exclusive(x_1189)) {
 lean_ctor_release(x_1189, 0);
 lean_ctor_release(x_1189, 1);
 x_1234 = x_1189;
} else {
 lean_dec_ref(x_1189);
 x_1234 = lean_box(0);
}
if (lean_is_scalar(x_1234)) {
 x_1235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1235 = x_1234;
}
lean_ctor_set(x_1235, 0, x_1232);
lean_ctor_set(x_1235, 1, x_1233);
return x_1235;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1185);
lean_dec(x_1183);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1077);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1236 = lean_ctor_get(x_1186, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1186, 1);
lean_inc(x_1237);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1238 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1238 = lean_box(0);
}
if (lean_is_scalar(x_1238)) {
 x_1239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1239 = x_1238;
}
lean_ctor_set(x_1239, 0, x_1236);
lean_ctor_set(x_1239, 1, x_1237);
return x_1239;
}
}
default: 
{
lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1118);
lean_dec(x_1113);
lean_dec(x_19);
x_1240 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1241 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_1240, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; 
x_1242 = lean_ctor_get(x_1241, 1);
lean_inc(x_1242);
lean_dec(x_1241);
if (lean_is_scalar(x_1083)) {
 x_1243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1243 = x_1083;
}
lean_ctor_set(x_1243, 0, x_1081);
lean_ctor_set(x_1243, 1, x_1117);
if (lean_is_scalar(x_1080)) {
 x_1244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1244 = x_1080;
}
lean_ctor_set(x_1244, 0, x_1116);
lean_ctor_set(x_1244, 1, x_1243);
if (lean_is_scalar(x_1078)) {
 x_1245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1245 = x_1078;
}
lean_ctor_set(x_1245, 0, x_1077);
lean_ctor_set(x_1245, 1, x_1244);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1100);
lean_ctor_set(x_1246, 1, x_1245);
if (lean_is_scalar(x_1076)) {
 x_1247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1247 = x_1076;
}
lean_ctor_set(x_1247, 0, x_1115);
lean_ctor_set(x_1247, 1, x_1246);
lean_inc(x_4);
x_1248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1248, 0, x_4);
lean_ctor_set(x_1248, 1, x_1247);
x_1249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1249, 0, x_1248);
x_20 = x_1249;
x_21 = x_1242;
goto block_28;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1115);
lean_dec(x_1100);
lean_dec(x_1083);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1078);
lean_dec(x_1077);
lean_dec(x_1076);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_1250 = lean_ctor_get(x_1241, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1241, 1);
lean_inc(x_1251);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 lean_ctor_release(x_1241, 1);
 x_1252 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1252 = lean_box(0);
}
if (lean_is_scalar(x_1252)) {
 x_1253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1253 = x_1252;
}
lean_ctor_set(x_1253, 0, x_1250);
lean_ctor_set(x_1253, 1, x_1251);
return x_1253;
}
}
}
}
}
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_7 = x_26;
x_8 = x_24;
x_16 = x_21;
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
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2;
x_3 = lean_unsigned_to_nat(708u);
x_4 = lean_unsigned_to_nat(61u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_array_get_size(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_toSubarray___rarg(x_2, x_24, x_23);
x_26 = lean_box(0);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_22);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(x_5, x_6, x_7, x_26, x_5, x_8, x_9, x_32, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(x_44, x_43, x_10, x_26, x_42, x_11, x_45, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_41);
lean_dec(x_43);
lean_dec(x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_33, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
lean_ctor_set(x_33, 0, x_49);
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_dec(x_33);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
lean_dec(x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
if (x_10 == 0)
{
if (x_11 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l_Lean_mkAppN(x_12, x_2);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_31;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
x_30 = lean_array_get_size(x_29);
x_31 = l_Array_toSubarray___rarg(x_29, x_13, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
lean_inc(x_31);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_31);
x_34 = lean_array_size(x_19);
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_19, x_22, x_24, x_27, x_32, x_19, x_34, x_35, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
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
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_36, 0, x_50);
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_box(0);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_36, 1);
lean_inc(x_57);
lean_dec(x_36);
x_58 = lean_ctor_get(x_38, 0);
lean_inc(x_58);
lean_dec(x_38);
x_59 = lean_ctor_get(x_39, 0);
lean_inc(x_59);
lean_dec(x_39);
x_60 = lean_ctor_get(x_40, 0);
lean_inc(x_60);
lean_dec(x_40);
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
lean_dec(x_41);
x_62 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_63 = lean_box(0);
x_64 = lean_unbox(x_61);
lean_dec(x_61);
x_65 = lean_unbox(x_60);
lean_dec(x_60);
x_66 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_3, x_59, x_62, x_31, x_19, x_32, x_58, x_34, x_35, x_64, x_65, x_2, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_58);
lean_dec(x_19);
lean_dec(x_3);
return x_66;
}
}
else
{
uint8_t x_67; 
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
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
return x_36;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_36, 0);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_36);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_25);
x_73 = lean_ctor_get(x_3, 2);
lean_inc(x_73);
x_74 = lean_array_get_size(x_73);
x_75 = l_Array_toSubarray___rarg(x_73, x_13, x_74);
x_76 = lean_box(0);
x_77 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
lean_inc(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_size(x_19);
x_80 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_19, x_22, x_24, x_71, x_76, x_19, x_79, x_80, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
lean_dec(x_71);
lean_dec(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_75);
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
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
x_93 = 1;
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
lean_dec(x_83);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
lean_dec(x_84);
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
lean_dec(x_85);
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
lean_dec(x_86);
x_102 = l_Lean_PersistentHashMap_toArray___at_Lean_Meta_Simp_UsedSimps_toArray___spec__1___closed__1;
x_103 = lean_box(0);
x_104 = lean_unbox(x_101);
lean_dec(x_101);
x_105 = lean_unbox(x_100);
lean_dec(x_100);
x_106 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_3, x_99, x_102, x_75, x_19, x_76, x_98, x_79, x_80, x_104, x_105, x_2, x_103, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
lean_dec(x_98);
lean_dec(x_19);
lean_dec(x_3);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_75);
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
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_109 = x_81;
} else {
 lean_dec_ref(x_81);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
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
x_111 = !lean_is_exclusive(x_21);
if (x_111 == 0)
{
return x_21;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_21, 0);
x_113 = lean_ctor_get(x_21, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_21);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_17, x_18, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2___boxed(lean_object** _args) {
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
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___boxed(lean_object** _args) {
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
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___boxed(lean_object** _args) {
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
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4(x_1, x_19, x_3, x_4, x_5, x_20, x_21, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
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
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_23 = lean_unbox(x_10);
lean_dec(x_10);
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_22, x_23, x_24, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_25;
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
lean_object* x_21 = _args[20];
_start:
{
size_t x_22; size_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_24 = lean_unbox(x_10);
lean_dec(x_10);
x_25 = lean_unbox(x_11);
lean_dec(x_11);
x_26 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_23, x_24, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_26;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_mkCongrFun(x_6, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_box(0);
x_18 = lean_array_size(x_2);
x_19 = 0;
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_17, x_2, x_18, x_19, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_mkAppN(x_23, x_2);
lean_ctor_set(x_8, 0, x_22);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_8);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_mkAppN(x_29, x_2);
lean_ctor_set(x_8, 0, x_27);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_8);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_8);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_box(0);
x_40 = lean_array_size(x_2);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_39, x_2, x_40, x_41, x_38, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
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
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_mkAppN(x_46, x_2);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
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
l_Lean_Meta_Simp_instInhabitedContext___closed__4 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__4);
l_Lean_Meta_Simp_instInhabitedContext___closed__5 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__5();
l_Lean_Meta_Simp_instInhabitedContext___closed__6 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__6);
l_Lean_Meta_Simp_instInhabitedContext___closed__7 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__7);
l_Lean_Meta_Simp_instInhabitedContext___closed__8 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__8);
l_Lean_Meta_Simp_instInhabitedContext___closed__9 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__9);
l_Lean_Meta_Simp_instInhabitedContext___closed__10 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__10);
l_Lean_Meta_Simp_instInhabitedContext___closed__11 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__11);
l_Lean_Meta_Simp_instInhabitedContext___closed__12 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__12);
l_Lean_Meta_Simp_instInhabitedContext___closed__13 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__13);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__1);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__2);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__3);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__4);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___closed__5);
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
l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__1();
l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__4___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5);
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
