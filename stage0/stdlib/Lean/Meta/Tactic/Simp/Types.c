// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Types
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.CongrTheorems Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems
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
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocOLeanEntry_keys___default;
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erased___default;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_simpTheorems___default;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_maxDischargeDepth___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object*);
static lean_object* l_Lean_Meta_Simp_Simprocs_pre___default___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_post___default;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
static uint32_t l_Lean_Meta_Simp_instInhabitedResult___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Meta_Simp_Context_maxDischargeDepth___default(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__6;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9(lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_pre___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_savingCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocOLeanEntry_post___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__4;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3___boxed(lean_object**);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__2;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_proof_x3f___default;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_removeUnnecessaryCasts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__4;
LEAN_EXPORT uint32_t l_Lean_Meta_Simp_Context_dischargeDepth___default;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getDtConfig___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_config___default___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Meta_Simp_Result_dischargeDepth___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__9;
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpDtConfig;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__7;
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
static lean_object* l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__3;
static uint32_t l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getDtConfig___closed__1;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkImpCongr___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_simprocNames___default;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__13;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_congrCache___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___closed__1;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_getDtConfig___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__5;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig___boxed(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1;
static lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__6;
static lean_object* l_Lean_Meta_Simp_instInhabitedStep___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_savingCache(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_config___default;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_usedTheorems___default;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_numSteps___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2___boxed(lean_object**);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_parent_x3f___default;
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__5___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Result_cache___default;
static lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__4;
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_cache___default;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__1;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4;
static lean_object* _init_l_Lean_Meta_Simp_Result_proof_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint32_t _init_l_Lean_Meta_Simp_Result_dischargeDepth___default() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Simp_Result_cache___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static uint32_t _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedResult___closed__1;
x_3 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_uint32(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__3;
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
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get_uint32(x_3, sizeof(void*)*2);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set_uint32(x_16, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 4, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
if (x_2 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; 
lean_ctor_set(x_3, 1, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get_uint32(x_3, sizeof(void*)*2);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
lean_inc(x_26);
lean_dec(x_3);
if (x_2 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set_uint32(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 4, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint32(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_38 = x_3;
} else {
 lean_dec_ref(x_3);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
if (x_2 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 5);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set_uint32(x_41, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 5);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set_uint32(x_43, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 4, x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = l_Lean_Meta_mkEqTrans(x_45, x_50, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_19, 0, x_53);
if (x_2 == 0)
{
uint8_t x_54; 
x_54 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_54);
lean_ctor_set(x_51, 0, x_3);
return x_51;
}
else
{
lean_ctor_set(x_51, 0, x_3);
return x_51;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
lean_ctor_set(x_19, 0, x_55);
if (x_2 == 0)
{
uint8_t x_57; lean_object* x_58; 
x_57 = 0;
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_19);
lean_free_object(x_3);
lean_dec(x_47);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
return x_51;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
lean_dec(x_19);
x_65 = l_Lean_Meta_mkEqTrans(x_45, x_64, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
if (x_2 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = 0;
lean_ctor_set(x_3, 1, x_69);
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 4, x_70);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
else
{
lean_object* x_72; 
lean_ctor_set(x_3, 1, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_3);
lean_dec(x_47);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_77; uint32_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_3, 0);
x_78 = lean_ctor_get_uint32(x_3, sizeof(void*)*2);
x_79 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
lean_inc(x_77);
lean_dec(x_3);
x_80 = lean_ctor_get(x_19, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_81 = x_19;
} else {
 lean_dec_ref(x_19);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_mkEqTrans(x_45, x_80, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_81;
}
lean_ctor_set(x_86, 0, x_83);
if (x_2 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set_uint32(x_88, sizeof(void*)*2, x_78);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 4, x_87);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_90, 0, x_77);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set_uint32(x_90, sizeof(void*)*2, x_78);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 4, x_79);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_84);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_81);
lean_dec(x_77);
x_92 = lean_ctor_get(x_82, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_94 = x_82;
} else {
 lean_dec_ref(x_82);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
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
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
lean_dec(x_1);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_config___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 16);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_config___default___closed__1;
return x_1;
}
}
LEAN_EXPORT uint32_t l_Lean_Meta_Simp_Context_maxDischargeDepth___default(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_UInt32_ofNatTruncate(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_maxDischargeDepth___default___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_Context_maxDischargeDepth___default(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_simpTheorems___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_3 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_parent_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint32_t _init_l_Lean_Meta_Simp_Context_dischargeDepth___default() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 16);
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
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__1;
x_3 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
x_4 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
x_5 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
x_6 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint32(x_6, sizeof(void*)*4, x_3);
lean_ctor_set_uint32(x_6, sizeof(void*)*4 + 4, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_Context_isDeclToUnfold(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
static uint32_t _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_12 = lean_array_push(x_11, x_6);
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Lean_Meta_Simp_Context_config___default___closed__1;
x_16 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_17 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set_uint32(x_17, sizeof(void*)*4, x_16);
lean_ctor_set_uint32(x_17, sizeof(void*)*4 + 4, x_14);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3;
x_21 = lean_array_push(x_20, x_6);
x_22 = lean_box(0);
x_23 = 0;
x_24 = l_Lean_Meta_Simp_Context_config___default___closed__1;
x_25 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_26 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint32(x_26, sizeof(void*)*4, x_25);
lean_ctor_set_uint32(x_26, sizeof(void*)*4 + 4, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_mkDefault___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Context_mkDefault(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_cache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_congrCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_usedTheorems___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_numSteps___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
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
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__3;
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
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
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
static uint8_t _init_l_Lean_Meta_Simp_SimprocOLeanEntry_post___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_SimprocOLeanEntry_keys___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
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
static lean_object* _init_l_Lean_Meta_Simp_Simprocs_pre___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Simprocs_pre___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Simprocs_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Simprocs_post___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Simprocs_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Simprocs_simprocNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Simprocs_erased___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
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
x_1 = l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Methods_pre___default___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Methods_pre___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint32_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = 0;
x_12 = 1;
x_13 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint32(x_13, sizeof(void*)*2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 4, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Methods_post___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Methods_discharge_x3f___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
x_2 = l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
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
lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*4);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get_uint32(x_4, sizeof(void*)*4 + 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set_uint32(x_21, sizeof(void*)*4, x_16);
lean_ctor_set_uint32(x_21, sizeof(void*)*4 + 4, x_19);
x_22 = lean_apply_8(x_2, x_3, x_21, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_savingCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_st_ref_set(x_4, x_38, x_27);
lean_dec(x_4);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_dec(x_22);
x_45 = lean_st_ref_take(x_4, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
lean_ctor_set(x_46, 0, x_13);
x_50 = lean_st_ref_set(x_4, x_46, x_47);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_43);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_46, 1);
x_56 = lean_ctor_get(x_46, 2);
x_57 = lean_ctor_get(x_46, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_st_ref_set(x_4, x_58, x_47);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_15, 1);
x_64 = lean_ctor_get(x_15, 2);
x_65 = lean_ctor_get(x_15, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_66 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_st_ref_set(x_4, x_67, x_16);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
lean_inc(x_4);
x_70 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_take(x_4, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 4, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_13);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_78);
x_81 = lean_st_ref_set(x_4, x_80, x_75);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_dec(x_70);
x_87 = lean_st_ref_take(x_4, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_13);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_st_ref_set(x_4, x_94, x_89);
lean_dec(x_4);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_85);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_savingCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_savingCache___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_5, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_5, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_1);
lean_inc(x_5);
x_25 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_14);
x_33 = lean_st_ref_set(x_5, x_29, x_30);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_26);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_ctor_get(x_29, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_st_ref_set(x_5, x_41, x_30);
lean_dec(x_5);
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
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_st_ref_take(x_5, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
lean_ctor_set(x_49, 0, x_14);
x_53 = lean_st_ref_set(x_5, x_49, x_50);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_46);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_49, 1);
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_14);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_st_ref_set(x_5, x_61, x_50);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; uint32_t x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_4, 0);
x_67 = lean_ctor_get_uint32(x_4, sizeof(void*)*4);
x_68 = lean_ctor_get(x_4, 2);
x_69 = lean_ctor_get(x_4, 3);
x_70 = lean_ctor_get_uint32(x_4, sizeof(void*)*4 + 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_dec(x_4);
x_71 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_1);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set_uint32(x_71, sizeof(void*)*4, x_67);
lean_ctor_set_uint32(x_71, sizeof(void*)*4 + 4, x_70);
lean_inc(x_5);
x_72 = lean_apply_8(x_2, x_3, x_71, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_take(x_5, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 3);
lean_inc(x_80);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 4, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_14);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
x_83 = lean_st_ref_set(x_5, x_82, x_77);
lean_dec(x_5);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_dec(x_72);
x_89 = lean_st_ref_take(x_5, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 3);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 4, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_14);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
x_97 = lean_st_ref_set(x_5, x_96, x_91);
lean_dec(x_5);
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
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_87);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint32_t x_109; lean_object* x_110; lean_object* x_111; uint32_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_16, 1);
x_102 = lean_ctor_get(x_16, 2);
x_103 = lean_ctor_get(x_16, 3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_16);
x_104 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
x_106 = lean_st_ref_set(x_5, x_105, x_17);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_ctor_get(x_4, 0);
lean_inc(x_108);
x_109 = lean_ctor_get_uint32(x_4, sizeof(void*)*4);
x_110 = lean_ctor_get(x_4, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 3);
lean_inc(x_111);
x_112 = lean_ctor_get_uint32(x_4, sizeof(void*)*4 + 4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_113 = x_4;
} else {
 lean_dec_ref(x_4);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 4, 8);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_1);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint32(x_114, sizeof(void*)*4, x_109);
lean_ctor_set_uint32(x_114, sizeof(void*)*4 + 4, x_112);
lean_inc(x_5);
x_115 = lean_apply_8(x_2, x_3, x_114, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_take(x_5, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 4, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_14);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_122);
lean_ctor_set(x_125, 3, x_123);
x_126 = lean_st_ref_set(x_5, x_125, x_120);
lean_dec(x_5);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_130 = lean_ctor_get(x_115, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_115, 1);
lean_inc(x_131);
lean_dec(x_115);
x_132 = lean_st_ref_take(x_5, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 3);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_14);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_137);
x_140 = lean_st_ref_set(x_5, x_139, x_134);
lean_dec(x_5);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_5, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_5, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 2);
lean_dec(x_24);
lean_ctor_set(x_3, 2, x_1);
lean_inc(x_5);
x_25 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_14);
x_33 = lean_st_ref_set(x_5, x_29, x_30);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_26);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_ctor_get(x_29, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_st_ref_set(x_5, x_41, x_30);
lean_dec(x_5);
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
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_st_ref_take(x_5, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
lean_ctor_set(x_49, 0, x_14);
x_53 = lean_st_ref_set(x_5, x_49, x_50);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_46);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_49, 1);
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_14);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_st_ref_set(x_5, x_61, x_50);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_1);
lean_inc(x_5);
x_69 = lean_apply_8(x_2, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_take(x_5, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 3);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_14);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
x_80 = lean_st_ref_set(x_5, x_79, x_74);
lean_dec(x_5);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_69, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
lean_dec(x_69);
x_86 = lean_st_ref_take(x_5, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_14);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
x_94 = lean_st_ref_set(x_5, x_93, x_88);
lean_dec(x_5);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_84);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_98 = lean_ctor_get(x_16, 1);
x_99 = lean_ctor_get(x_16, 2);
x_100 = lean_ctor_get(x_16, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_16);
x_101 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_100);
x_103 = lean_st_ref_set(x_5, x_102, x_17);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_3, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_107 = x_3;
} else {
 lean_dec_ref(x_3);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 3, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_1);
lean_inc(x_5);
x_109 = lean_apply_8(x_2, x_108, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_st_ref_take(x_5, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 x_118 = x_113;
} else {
 lean_dec_ref(x_113);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_14);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_116);
lean_ctor_set(x_119, 3, x_117);
x_120 = lean_st_ref_set(x_5, x_119, x_114);
lean_dec(x_5);
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
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_124 = lean_ctor_get(x_109, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_109, 1);
lean_inc(x_125);
lean_dec(x_109);
x_126 = lean_st_ref_take(x_5, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 3);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 4, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_14);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set(x_133, 2, x_130);
lean_ctor_set(x_133, 3, x_131);
x_134 = lean_st_ref_set(x_5, x_133, x_128);
lean_dec(x_5);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withDischarger___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Meta_Origin_key(x_4);
x_7 = l_Lean_Meta_Origin_key(x_1);
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Meta_Origin_key(x_2);
x_6 = l_Lean_Name_hash___override(x_5);
lean_dec(x_5);
x_7 = lean_hashmap_mk_idx(x_4, x_6);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Meta_Origin_key(x_4);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = lean_hashmap_mk_idx(x_6, x_8);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Meta_Origin_key(x_13);
x_18 = l_Lean_Name_hash___override(x_17);
lean_dec(x_17);
x_19 = lean_hashmap_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_Meta_Origin_key(x_6);
x_10 = l_Lean_Meta_Origin_key(x_1);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = l_Lean_Meta_Origin_key(x_13);
x_17 = l_Lean_Meta_Origin_key(x_1);
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Meta_Origin_key(x_2);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
lean_inc(x_7);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Meta_Origin_key(x_2);
x_26 = l_Lean_Name_hash___override(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_27 = lean_hashmap_mk_idx(x_24, x_26);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
lean_inc(x_1);
lean_inc(x_15);
x_17 = l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(x_15, x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_11, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_11, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(x_15, x_1, x_23);
lean_ctor_set(x_11, 2, x_24);
x_25 = lean_st_ref_set(x_4, x_11, x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
x_33 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(x_15, x_1, x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_14);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_16);
x_35 = lean_st_ref_set(x_4, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_40 = lean_st_ref_set(x_4, x_11, x_12);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Expr_app___override(x_9, x_2);
x_11 = lean_box(0);
x_12 = 0;
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 4, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_2);
x_18 = l_Lean_Meta_mkCongrFun(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Expr_app___override(x_21, x_2);
lean_ctor_set(x_8, 0, x_20);
x_23 = 0;
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set_uint32(x_25, sizeof(void*)*2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_Expr_app___override(x_28, x_2);
lean_ctor_set(x_8, 0, x_26);
x_30 = 0;
x_31 = 1;
x_32 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_8);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
lean_inc(x_2);
x_39 = l_Lean_Meta_mkCongrFun(x_38, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
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
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_Expr_app___override(x_43, x_2);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_46 = 0;
x_47 = 1;
x_48 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 4, x_47);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
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
lean_object* x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = 0;
x_15 = 1;
x_16 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set_uint32(x_16, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 4, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = l_Lean_Meta_mkCongrArg(x_8, x_19, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_12, 0, x_22);
x_23 = 0;
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set_uint32(x_25, sizeof(void*)*2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; uint32_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_26);
x_28 = 0;
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set_uint32(x_30, sizeof(void*)*2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_12);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = l_Lean_Meta_mkCongrArg(x_8, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = 0;
x_43 = 1;
x_44 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set_uint32(x_44, sizeof(void*)*2, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2 + 4, x_43);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_48 = x_37;
} else {
 lean_dec_ref(x_37);
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
else
{
lean_object* x_50; 
lean_dec(x_8);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_dec(x_2);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = l_Lean_Meta_mkCongrFun(x_52, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint32_t x_56; uint8_t x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_11, 0, x_55);
x_56 = 0;
x_57 = 1;
x_58 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_58, 0, x_10);
lean_ctor_set(x_58, 1, x_11);
lean_ctor_set_uint32(x_58, sizeof(void*)*2, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 4, x_57);
lean_ctor_set(x_53, 0, x_58);
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
lean_ctor_set(x_11, 0, x_59);
x_61 = 0;
x_62 = 1;
x_63 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_63, 0, x_10);
lean_ctor_set(x_63, 1, x_11);
lean_ctor_set_uint32(x_63, sizeof(void*)*2, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*2 + 4, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_free_object(x_11);
lean_dec(x_10);
x_65 = !lean_is_exclusive(x_53);
if (x_65 == 0)
{
return x_53;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_53);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
lean_dec(x_11);
x_70 = l_Lean_Meta_mkCongrFun(x_69, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint32_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_75 = 0;
x_76 = 1;
x_77 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_77, 0, x_10);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set_uint32(x_77, sizeof(void*)*2, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*2 + 4, x_76);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_10);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_9);
x_83 = lean_ctor_get(x_11, 0);
lean_inc(x_83);
lean_dec(x_11);
x_84 = !lean_is_exclusive(x_50);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_50, 0);
x_86 = l_Lean_Meta_mkCongr(x_83, x_85, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint32_t x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
lean_ctor_set(x_50, 0, x_88);
x_89 = 0;
x_90 = 1;
x_91 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_91, 0, x_10);
lean_ctor_set(x_91, 1, x_50);
lean_ctor_set_uint32(x_91, sizeof(void*)*2, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*2 + 4, x_90);
lean_ctor_set(x_86, 0, x_91);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; uint32_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_86, 0);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_86);
lean_ctor_set(x_50, 0, x_92);
x_94 = 0;
x_95 = 1;
x_96 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_96, 0, x_10);
lean_ctor_set(x_96, 1, x_50);
lean_ctor_set_uint32(x_96, sizeof(void*)*2, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 4, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_free_object(x_50);
lean_dec(x_10);
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
x_102 = lean_ctor_get(x_50, 0);
lean_inc(x_102);
lean_dec(x_50);
x_103 = l_Lean_Meta_mkCongr(x_83, x_102, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint32_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_104);
x_108 = 0;
x_109 = 1;
x_110 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set_uint32(x_110, sizeof(void*)*2, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2 + 4, x_109);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_10);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
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
x_1 = lean_mk_string_from_bytes("Lean.Expr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateForallE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forall expected", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkImpCongr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_mkImpCongr___closed__1;
x_2 = l_Lean_Meta_Simp_mkImpCongr___closed__2;
x_3 = lean_unsigned_to_nat(1706u);
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
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; size_t x_143; size_t x_144; uint8_t x_145; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_142 = l_Lean_Expr_forallE___override(x_138, x_139, x_140, x_141);
x_143 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_144 = lean_ptr_addr(x_9);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_142);
lean_dec(x_140);
x_146 = l_Lean_Expr_forallE___override(x_138, x_9, x_10, x_141);
x_12 = x_146;
goto block_137;
}
else
{
size_t x_147; size_t x_148; uint8_t x_149; 
x_147 = lean_ptr_addr(x_140);
lean_dec(x_140);
x_148 = lean_ptr_addr(x_10);
x_149 = lean_usize_dec_eq(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_142);
x_150 = l_Lean_Expr_forallE___override(x_138, x_9, x_10, x_141);
x_12 = x_150;
goto block_137;
}
else
{
uint8_t x_151; 
x_151 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_141, x_141);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_142);
x_152 = l_Lean_Expr_forallE___override(x_138, x_9, x_10, x_141);
x_12 = x_152;
goto block_137;
}
else
{
lean_dec(x_138);
lean_dec(x_10);
lean_dec(x_9);
x_12 = x_142;
goto block_137;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_153 = l_Lean_Meta_Simp_mkImpCongr___closed__4;
x_154 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_153);
x_12 = x_154;
goto block_137;
}
block_137:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = 0;
x_16 = 1;
x_17 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set_uint32(x_17, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 4, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_mkImpCongr(x_22, x_25, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_13, 0, x_29);
x_30 = 0;
x_31 = 1;
x_32 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 4, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; uint32_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
lean_ctor_set(x_13, 0, x_33);
x_35 = 0;
x_36 = 1;
x_37 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set_uint32(x_37, sizeof(void*)*2, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 4, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_13);
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_mkImpCongr(x_52, x_55, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint32_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
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
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_62 = 0;
x_63 = 1;
x_64 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set_uint32(x_64, sizeof(void*)*2, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*2 + 4, x_63);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_12);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_68 = x_57;
} else {
 lean_dec_ref(x_57);
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
lean_dec(x_52);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_72 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_51, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_51, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_76 = x_51;
} else {
 lean_dec_ref(x_51);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_11);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_11, 0);
lean_dec(x_79);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_80 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_83 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_mkImpCongr(x_81, x_84, x_4, x_5, x_6, x_7, x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint32_t x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
lean_ctor_set(x_11, 0, x_88);
x_89 = 0;
x_90 = 1;
x_91 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_11);
lean_ctor_set_uint32(x_91, sizeof(void*)*2, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*2 + 4, x_90);
lean_ctor_set(x_86, 0, x_91);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; uint32_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_86, 0);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_86);
lean_ctor_set(x_11, 0, x_92);
x_94 = 0;
x_95 = 1;
x_96 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_96, 0, x_12);
lean_ctor_set(x_96, 1, x_11);
lean_ctor_set_uint32(x_96, sizeof(void*)*2, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 4, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_free_object(x_11);
lean_dec(x_12);
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
uint8_t x_102; 
lean_dec(x_81);
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_83);
if (x_102 == 0)
{
return x_83;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_83, 0);
x_104 = lean_ctor_get(x_83, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_83);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_80);
if (x_106 == 0)
{
return x_80;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_80, 0);
x_108 = lean_ctor_get(x_80, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_80);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_110 = l_Lean_Meta_Simp_Result_getProof(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l_Lean_Meta_Simp_Result_getProof(x_3, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Meta_mkImpCongr(x_111, x_114, x_4, x_5, x_6, x_7, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint32_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
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
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_117);
x_121 = 0;
x_122 = 1;
x_123 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_123, 0, x_12);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set_uint32(x_123, sizeof(void*)*2, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*2 + 4, x_122);
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_12);
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_111);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_131 = x_113;
} else {
 lean_dec_ref(x_113);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_ctor_get(x_110, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_110, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_135 = x_110;
} else {
 lean_dec_ref(x_110);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
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
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
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
x_1 = lean_mk_string_from_bytes("ndrec", 5);
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
x_1 = lean_mk_string_from_bytes("refl", 4);
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
x_4 = l_Lean_Expr_appFn_x21(x_3);
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
x_22 = l___private_Init_Util_0__outOfBounds___rarg(x_21);
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
x_47 = l___private_Init_Util_0__outOfBounds___rarg(x_46);
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
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_16, 3);
x_20 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
x_21 = 0;
x_22 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
lean_inc(x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___rarg(x_19, x_23);
lean_ctor_set(x_16, 3, x_24);
x_25 = lean_st_ref_set(x_9, x_16, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
x_34 = lean_ctor_get(x_16, 2);
x_35 = lean_ctor_get(x_16, 3);
x_36 = lean_ctor_get(x_16, 4);
x_37 = lean_ctor_get(x_16, 5);
x_38 = lean_ctor_get(x_16, 6);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_39 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
x_40 = 0;
x_41 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_13);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
lean_inc(x_11);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_PersistentArray_push___rarg(x_35, x_42);
x_44 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_36);
lean_ctor_set(x_44, 5, x_37);
lean_ctor_set(x_44, 6, x_38);
x_45 = lean_st_ref_set(x_9, x_44, x_17);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
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
x_1 = lean_mk_string_from_bytes("Debug", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
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
x_1 = lean_mk_string_from_bytes("app [", 5);
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
x_1 = lean_mk_string_from_bytes("] ", 2);
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
x_1 = lean_mk_string_from_bytes(" ", 1);
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
x_1 = lean_mk_string_from_bytes(" hasFwdDeps: ", 13);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_dec(x_93);
lean_inc(x_27);
x_106 = l_Nat_repr(x_27);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__8;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__10;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Nat_repr(x_30);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__12;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_17);
x_119 = l_Lean_MessageData_ofExpr(x_17);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__14;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_fget(x_2, x_27);
x_124 = lean_ctor_get_uint8(x_123, sizeof(void*)*1 + 1);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_125 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__19;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_128, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_105);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_130, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_131);
lean_dec(x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_18 = x_133;
x_19 = x_134;
goto block_26;
}
else
{
uint8_t x_135; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_122);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_92, x_142, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_105);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___lambda__2(x_17, x_29, x_27, x_2, x_1, x_28, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_145);
lean_dec(x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_18 = x_147;
x_19 = x_148;
goto block_26;
}
else
{
uint8_t x_149; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
return x_146;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_146, 0);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_146);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Meta_Simp_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_17 = l_Lean_Meta_getFunInfoNArgs(x_15, x_16, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3(x_13, x_20, x_2, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_20);
lean_dec(x_13);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_10);
return x_41;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__5(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9(lean_object* x_1, size_t x_2, size_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = 1;
lean_inc(x_1);
x_20 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_2, x_3, x_19, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_21);
x_28 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_27, x_1, x_21);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_st_ref_set(x_7, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
lean_inc(x_21);
x_38 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_35, x_1, x_21);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
x_40 = lean_st_ref_set(x_7, x_39, x_25);
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
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_48);
return x_13;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_HashMapImp_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__1(x_51, x_1);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; lean_object* x_54; 
x_53 = 1;
lean_inc(x_1);
x_54 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_2, x_3, x_53, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_7, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
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
lean_inc(x_55);
x_65 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__3(x_61, x_1, x_55);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 4, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
x_67 = lean_st_ref_set(x_7, x_66, x_59);
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
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_54, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_73 = x_54;
} else {
 lean_dec_ref(x_54);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
lean_dec(x_52);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_50);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_2);
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
lean_inc(x_12);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_24 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9(x_16, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_37 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9(x_28, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_14 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__9(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Tactic.Simp.Types", 27);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(414u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_dec(x_10);
x_19 = lean_box(x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = lean_dsimp(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_5, x_21);
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_23, x_6, x_7, x_8, x_9, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
return x_25;
}
else
{
uint8_t x_26; 
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
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1___boxed), 16, 1);
lean_closure_set(x_30, 0, x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_31 = lean_simp(x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_32);
x_34 = lean_array_push(x_4, x_32);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_35);
x_36 = lean_array_push(x_5, x_35);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_3, x_35, x_30, x_34, x_36, x_6, x_8, x_7, x_9, x_38, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_33);
lean_dec(x_35);
lean_dec(x_3);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_40 = 1;
x_41 = lean_box(0);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_3, x_35, x_30, x_34, x_36, x_6, x_8, x_40, x_9, x_41, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_33);
lean_dec(x_35);
lean_dec(x_3);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_30);
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
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 3:
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_array_push(x_5, x_3);
x_48 = 1;
x_49 = lean_box(0);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_47, x_48, x_7, x_8, x_9, x_49, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
return x_50;
}
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_array_push(x_5, x_3);
x_52 = lean_box(0);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_51, x_6, x_7, x_8, x_9, x_52, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
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
default: 
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
lean_dec(x_3);
x_54 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_55 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1(x_54, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_56, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_57);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_56);
lean_dec(x_8);
return x_58;
}
else
{
uint8_t x_59; 
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
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
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
x_60 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_25, x_52, x_18, x_28, x_31, x_57, x_58, x_40, x_59, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_83 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_25, x_52, x_18, x_28, x_31, x_80, x_81, x_40, x_82, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_106 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_25, x_52, x_18, x_28, x_31, x_103, x_104, x_40, x_105, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_138 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_132, x_129, x_18, x_28, x_31, x_135, x_136, x_40, x_137, x_134, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_159 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_132, x_129, x_18, x_28, x_31, x_156, x_157, x_40, x_158, x_155, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_180 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_132, x_129, x_18, x_28, x_31, x_177, x_178, x_40, x_179, x_176, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_219 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_213, x_210, x_18, x_28, x_31, x_216, x_217, x_200, x_218, x_215, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_240 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_213, x_210, x_18, x_28, x_31, x_237, x_238, x_200, x_239, x_236, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_261 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_213, x_210, x_18, x_28, x_31, x_258, x_259, x_200, x_260, x_257, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_304 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_298, x_295, x_18, x_28, x_31, x_301, x_302, x_283, x_303, x_300, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_325 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_298, x_295, x_18, x_28, x_31, x_322, x_323, x_283, x_324, x_321, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_346 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_298, x_295, x_18, x_28, x_31, x_343, x_344, x_283, x_345, x_342, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_393 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_387, x_384, x_18, x_28, x_31, x_390, x_391, x_371, x_392, x_389, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_414 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_387, x_384, x_18, x_28, x_31, x_411, x_412, x_371, x_413, x_410, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_435 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_387, x_384, x_18, x_28, x_31, x_432, x_433, x_371, x_434, x_431, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_486 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_480, x_477, x_18, x_28, x_458, x_483, x_484, x_463, x_485, x_482, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_507 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_480, x_477, x_18, x_28, x_458, x_504, x_505, x_463, x_506, x_503, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_528 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_480, x_477, x_18, x_28, x_458, x_525, x_526, x_463, x_527, x_524, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_583 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_577, x_574, x_18, x_552, x_553, x_580, x_581, x_559, x_582, x_579, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_604 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_577, x_574, x_18, x_552, x_553, x_601, x_602, x_559, x_603, x_600, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_625 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_577, x_574, x_18, x_552, x_553, x_622, x_623, x_559, x_624, x_621, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_684 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_678, x_675, x_18, x_651, x_653, x_681, x_682, x_659, x_683, x_680, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_705 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_678, x_675, x_18, x_651, x_653, x_702, x_703, x_659, x_704, x_701, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_726 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_678, x_675, x_18, x_651, x_653, x_723, x_724, x_659, x_725, x_722, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_7);
x_16 = l_Lean_Expr_app___override(x_4, x_7);
x_17 = lean_array_push(x_5, x_7);
x_18 = l_Lean_Expr_bindingBody_x21(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(473u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congr", 5);
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
x_1 = lean_mk_string_from_bytes("failed to synthesize instance", 29);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
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
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 2);
lean_inc(x_45);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_17);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_27);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_18 = x_48;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_32, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_32, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_32, 0);
lean_dec(x_52);
x_53 = lean_array_fget(x_43, x_44);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_44, x_55);
lean_dec(x_44);
lean_ctor_set(x_32, 1, x_56);
lean_inc(x_17);
x_57 = l_Lean_Expr_app___override(x_38, x_17);
lean_inc(x_17);
x_58 = lean_array_push(x_41, x_17);
x_59 = l_Lean_Expr_bindingBody_x21(x_42);
lean_dec(x_42);
x_60 = lean_box(x_54);
switch (lean_obj_tag(x_60)) {
case 1:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_17);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_ctor_set(x_30, 1, x_59);
lean_ctor_set(x_30, 0, x_58);
lean_ctor_set(x_29, 0, x_57);
lean_inc(x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_27);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_18 = x_65;
x_19 = x_63;
goto block_26;
}
else
{
uint8_t x_66; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 2:
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_array_get_size(x_1);
x_71 = lean_nat_dec_lt(x_35, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Lean_Meta_Simp_instInhabitedResult;
x_73 = l___private_Init_Util_0__outOfBounds___rarg(x_72);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_73);
x_74 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_73, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_nat_add(x_35, x_55);
lean_dec(x_35);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
lean_inc(x_75);
lean_inc(x_78);
x_79 = l_Lean_mkAppB(x_57, x_78, x_75);
x_80 = lean_array_push(x_58, x_78);
x_81 = lean_array_push(x_80, x_75);
x_82 = l_Lean_Expr_bindingBody_x21(x_59);
lean_dec(x_59);
x_83 = l_Lean_Expr_bindingBody_x21(x_82);
lean_dec(x_82);
lean_ctor_set(x_30, 1, x_83);
lean_ctor_set(x_30, 0, x_81);
lean_ctor_set(x_29, 0, x_79);
lean_ctor_set(x_28, 0, x_77);
lean_inc(x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_27);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_18 = x_85;
x_19 = x_76;
goto block_26;
}
else
{
uint8_t x_86; 
lean_dec(x_73);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_array_fget(x_1, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_90);
x_91 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_90, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_nat_add(x_35, x_55);
lean_dec(x_35);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
lean_inc(x_92);
lean_inc(x_95);
x_96 = l_Lean_mkAppB(x_57, x_95, x_92);
x_97 = lean_array_push(x_58, x_95);
x_98 = lean_array_push(x_97, x_92);
x_99 = l_Lean_Expr_bindingBody_x21(x_59);
lean_dec(x_59);
x_100 = l_Lean_Expr_bindingBody_x21(x_99);
lean_dec(x_99);
lean_ctor_set(x_30, 1, x_100);
lean_ctor_set(x_30, 0, x_98);
lean_ctor_set(x_29, 0, x_96);
lean_ctor_set(x_28, 0, x_94);
lean_inc(x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_27);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_18 = x_102;
x_19 = x_93;
goto block_26;
}
else
{
uint8_t x_103; 
lean_dec(x_90);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
return x_91;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
case 4:
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_17);
x_107 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_108 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_107, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_ctor_set(x_30, 1, x_59);
lean_ctor_set(x_30, 0, x_58);
lean_ctor_set(x_29, 0, x_57);
lean_inc(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_27);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_18 = x_111;
x_19 = x_109;
goto block_26;
}
else
{
uint8_t x_112; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 5:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_free_object(x_27);
x_116 = l_Lean_Expr_bindingDomain_x21(x_59);
x_117 = lean_expr_instantiate_rev(x_116, x_58);
lean_dec(x_116);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_118 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_117);
x_121 = l_Lean_Meta_isExprDefEq(x_119, x_117, x_10, x_11, x_12, x_13, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_17);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_117);
x_126 = l_Lean_Meta_trySynthInstance(x_117, x_125, x_10, x_11, x_12, x_13, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 1)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_117);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_2);
x_130 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_32, x_2, x_57, x_58, x_59, x_129, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_128);
lean_dec(x_59);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_18 = x_131;
x_19 = x_132;
goto block_26;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_127);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_135 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_134, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_117);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_box(0);
x_140 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_125, x_58, x_59, x_57, x_35, x_32, x_139, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_18 = x_141;
x_19 = x_142;
goto block_26;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
lean_dec(x_135);
x_144 = l_Lean_indentExpr(x_117);
x_145 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_134, x_148, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_143);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_125, x_58, x_59, x_57, x_35, x_32, x_150, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_151);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_18 = x_153;
x_19 = x_154;
goto block_26;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_117);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_126);
if (x_155 == 0)
{
return x_126;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_126, 0);
x_157 = lean_ctor_get(x_126, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_126);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_117);
x_159 = lean_ctor_get(x_121, 1);
lean_inc(x_159);
lean_dec(x_121);
lean_inc(x_2);
x_160 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_32, x_2, x_57, x_58, x_59, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_159);
lean_dec(x_59);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_18 = x_161;
x_19 = x_162;
goto block_26;
}
}
else
{
uint8_t x_163; 
lean_dec(x_117);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_121);
if (x_163 == 0)
{
return x_121;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_121, 0);
x_165 = lean_ctor_get(x_121, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_121);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_117);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_32);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_118);
if (x_167 == 0)
{
return x_118;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_118, 0);
x_169 = lean_ctor_get(x_118, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_118);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
default: 
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_60);
lean_dec(x_17);
lean_ctor_set(x_30, 1, x_59);
lean_ctor_set(x_30, 0, x_58);
lean_ctor_set(x_29, 0, x_57);
lean_inc(x_2);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_2);
lean_ctor_set(x_171, 1, x_27);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_18 = x_172;
x_19 = x_14;
goto block_26;
}
}
}
else
{
lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_32);
x_173 = lean_array_fget(x_43, x_44);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_44, x_175);
lean_dec(x_44);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_43);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_45);
lean_inc(x_17);
x_178 = l_Lean_Expr_app___override(x_38, x_17);
lean_inc(x_17);
x_179 = lean_array_push(x_41, x_17);
x_180 = l_Lean_Expr_bindingBody_x21(x_42);
lean_dec(x_42);
x_181 = lean_box(x_174);
switch (lean_obj_tag(x_181)) {
case 1:
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_17);
x_182 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_183 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_182, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
lean_ctor_set(x_30, 1, x_180);
lean_ctor_set(x_30, 0, x_179);
lean_ctor_set(x_29, 0, x_178);
lean_ctor_set(x_27, 0, x_177);
lean_inc(x_2);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_2);
lean_ctor_set(x_185, 1, x_27);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_18 = x_186;
x_19 = x_184;
goto block_26;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_189 = x_183;
} else {
 lean_dec_ref(x_183);
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
case 2:
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_array_get_size(x_1);
x_192 = lean_nat_dec_lt(x_35, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = l_Lean_Meta_Simp_instInhabitedResult;
x_194 = l___private_Init_Util_0__outOfBounds___rarg(x_193);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_194);
x_195 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_194, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_nat_add(x_35, x_175);
lean_dec(x_35);
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
lean_inc(x_196);
lean_inc(x_199);
x_200 = l_Lean_mkAppB(x_178, x_199, x_196);
x_201 = lean_array_push(x_179, x_199);
x_202 = lean_array_push(x_201, x_196);
x_203 = l_Lean_Expr_bindingBody_x21(x_180);
lean_dec(x_180);
x_204 = l_Lean_Expr_bindingBody_x21(x_203);
lean_dec(x_203);
lean_ctor_set(x_30, 1, x_204);
lean_ctor_set(x_30, 0, x_202);
lean_ctor_set(x_29, 0, x_200);
lean_ctor_set(x_28, 0, x_198);
lean_ctor_set(x_27, 0, x_177);
lean_inc(x_2);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_2);
lean_ctor_set(x_205, 1, x_27);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_18 = x_206;
x_19 = x_197;
goto block_26;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_194);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_207 = lean_ctor_get(x_195, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_195, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_209 = x_195;
} else {
 lean_dec_ref(x_195);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_array_fget(x_1, x_35);
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
x_215 = lean_nat_add(x_35, x_175);
lean_dec(x_35);
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
lean_dec(x_211);
lean_inc(x_213);
lean_inc(x_216);
x_217 = l_Lean_mkAppB(x_178, x_216, x_213);
x_218 = lean_array_push(x_179, x_216);
x_219 = lean_array_push(x_218, x_213);
x_220 = l_Lean_Expr_bindingBody_x21(x_180);
lean_dec(x_180);
x_221 = l_Lean_Expr_bindingBody_x21(x_220);
lean_dec(x_220);
lean_ctor_set(x_30, 1, x_221);
lean_ctor_set(x_30, 0, x_219);
lean_ctor_set(x_29, 0, x_217);
lean_ctor_set(x_28, 0, x_215);
lean_ctor_set(x_27, 0, x_177);
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
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
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
}
case 4:
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_17);
x_228 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_229 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_228, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
lean_ctor_set(x_30, 1, x_180);
lean_ctor_set(x_30, 0, x_179);
lean_ctor_set(x_29, 0, x_178);
lean_ctor_set(x_27, 0, x_177);
lean_inc(x_2);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_2);
lean_ctor_set(x_231, 1, x_27);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_18 = x_232;
x_19 = x_230;
goto block_26;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_235 = x_229;
} else {
 lean_dec_ref(x_229);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
case 5:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_free_object(x_30);
lean_free_object(x_29);
lean_free_object(x_28);
lean_free_object(x_27);
x_237 = l_Lean_Expr_bindingDomain_x21(x_180);
x_238 = lean_expr_instantiate_rev(x_237, x_179);
lean_dec(x_237);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_239 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_238);
x_242 = l_Lean_Meta_isExprDefEq(x_240, x_238, x_10, x_11, x_12, x_13, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_17);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_238);
x_247 = l_Lean_Meta_trySynthInstance(x_238, x_246, x_10, x_11, x_12, x_13, x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 1)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_238);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_2);
x_251 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_177, x_2, x_178, x_179, x_180, x_250, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_249);
lean_dec(x_180);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_18 = x_252;
x_19 = x_253;
goto block_26;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_248);
x_254 = lean_ctor_get(x_247, 1);
lean_inc(x_254);
lean_dec(x_247);
x_255 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_256 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_255, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_238);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_box(0);
x_261 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_246, x_179, x_180, x_178, x_35, x_177, x_260, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_259);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_18 = x_262;
x_19 = x_263;
goto block_26;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_264 = lean_ctor_get(x_256, 1);
lean_inc(x_264);
lean_dec(x_256);
x_265 = l_Lean_indentExpr(x_238);
x_266 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_255, x_269, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_264);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_246, x_179, x_180, x_178, x_35, x_177, x_271, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_272);
lean_dec(x_271);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_18 = x_274;
x_19 = x_275;
goto block_26;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_238);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_276 = lean_ctor_get(x_247, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_247, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_278 = x_247;
} else {
 lean_dec_ref(x_247);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_238);
x_280 = lean_ctor_get(x_242, 1);
lean_inc(x_280);
lean_dec(x_242);
lean_inc(x_2);
x_281 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_177, x_2, x_178, x_179, x_180, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_280);
lean_dec(x_180);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_18 = x_282;
x_19 = x_283;
goto block_26;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_238);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_284 = lean_ctor_get(x_242, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_242, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_286 = x_242;
} else {
 lean_dec_ref(x_242);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_238);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_288 = lean_ctor_get(x_239, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_239, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_290 = x_239;
} else {
 lean_dec_ref(x_239);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
default: 
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_181);
lean_dec(x_17);
lean_ctor_set(x_30, 1, x_180);
lean_ctor_set(x_30, 0, x_179);
lean_ctor_set(x_29, 0, x_178);
lean_ctor_set(x_27, 0, x_177);
lean_inc(x_2);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_2);
lean_ctor_set(x_292, 1, x_27);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_18 = x_293;
x_19 = x_14;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_30, 0);
x_295 = lean_ctor_get(x_30, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_30);
x_296 = lean_ctor_get(x_32, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_32, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_32, 2);
lean_inc(x_298);
x_299 = lean_nat_dec_lt(x_297, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_17);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_294);
lean_ctor_set(x_300, 1, x_295);
lean_ctor_set(x_29, 1, x_300);
lean_inc(x_2);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_2);
lean_ctor_set(x_301, 1, x_27);
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_18 = x_302;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_303 = x_32;
} else {
 lean_dec_ref(x_32);
 x_303 = lean_box(0);
}
x_304 = lean_array_fget(x_296, x_297);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_nat_add(x_297, x_306);
lean_dec(x_297);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(0, 3, 0);
} else {
 x_308 = x_303;
}
lean_ctor_set(x_308, 0, x_296);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 2, x_298);
lean_inc(x_17);
x_309 = l_Lean_Expr_app___override(x_38, x_17);
lean_inc(x_17);
x_310 = lean_array_push(x_294, x_17);
x_311 = l_Lean_Expr_bindingBody_x21(x_295);
lean_dec(x_295);
x_312 = lean_box(x_305);
switch (lean_obj_tag(x_312)) {
case 1:
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_17);
x_313 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_314 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_313, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_29, 1, x_316);
lean_ctor_set(x_29, 0, x_309);
lean_ctor_set(x_27, 0, x_308);
lean_inc(x_2);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_2);
lean_ctor_set(x_317, 1, x_27);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_18 = x_318;
x_19 = x_315;
goto block_26;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_319 = lean_ctor_get(x_314, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_314, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_321 = x_314;
} else {
 lean_dec_ref(x_314);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
case 2:
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_array_get_size(x_1);
x_324 = lean_nat_dec_lt(x_35, x_323);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = l_Lean_Meta_Simp_instInhabitedResult;
x_326 = l___private_Init_Util_0__outOfBounds___rarg(x_325);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_326);
x_327 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_326, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_nat_add(x_35, x_306);
lean_dec(x_35);
x_331 = lean_ctor_get(x_326, 0);
lean_inc(x_331);
lean_dec(x_326);
lean_inc(x_328);
lean_inc(x_331);
x_332 = l_Lean_mkAppB(x_309, x_331, x_328);
x_333 = lean_array_push(x_310, x_331);
x_334 = lean_array_push(x_333, x_328);
x_335 = l_Lean_Expr_bindingBody_x21(x_311);
lean_dec(x_311);
x_336 = l_Lean_Expr_bindingBody_x21(x_335);
lean_dec(x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_336);
lean_ctor_set(x_29, 1, x_337);
lean_ctor_set(x_29, 0, x_332);
lean_ctor_set(x_28, 0, x_330);
lean_ctor_set(x_27, 0, x_308);
lean_inc(x_2);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_2);
lean_ctor_set(x_338, 1, x_27);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_18 = x_339;
x_19 = x_329;
goto block_26;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_326);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_340 = lean_ctor_get(x_327, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_327, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_342 = x_327;
} else {
 lean_dec_ref(x_327);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_array_fget(x_1, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_344);
x_345 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_344, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_nat_add(x_35, x_306);
lean_dec(x_35);
x_349 = lean_ctor_get(x_344, 0);
lean_inc(x_349);
lean_dec(x_344);
lean_inc(x_346);
lean_inc(x_349);
x_350 = l_Lean_mkAppB(x_309, x_349, x_346);
x_351 = lean_array_push(x_310, x_349);
x_352 = lean_array_push(x_351, x_346);
x_353 = l_Lean_Expr_bindingBody_x21(x_311);
lean_dec(x_311);
x_354 = l_Lean_Expr_bindingBody_x21(x_353);
lean_dec(x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set(x_29, 1, x_355);
lean_ctor_set(x_29, 0, x_350);
lean_ctor_set(x_28, 0, x_348);
lean_ctor_set(x_27, 0, x_308);
lean_inc(x_2);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_2);
lean_ctor_set(x_356, 1, x_27);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_18 = x_357;
x_19 = x_347;
goto block_26;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_344);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_358 = lean_ctor_get(x_345, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_345, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_360 = x_345;
} else {
 lean_dec_ref(x_345);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
case 4:
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_17);
x_362 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_363 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_362, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_310);
lean_ctor_set(x_365, 1, x_311);
lean_ctor_set(x_29, 1, x_365);
lean_ctor_set(x_29, 0, x_309);
lean_ctor_set(x_27, 0, x_308);
lean_inc(x_2);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_2);
lean_ctor_set(x_366, 1, x_27);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_18 = x_367;
x_19 = x_364;
goto block_26;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_free_object(x_29);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_370 = x_363;
} else {
 lean_dec_ref(x_363);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
case 5:
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_free_object(x_29);
lean_free_object(x_28);
lean_free_object(x_27);
x_372 = l_Lean_Expr_bindingDomain_x21(x_311);
x_373 = lean_expr_instantiate_rev(x_372, x_310);
lean_dec(x_372);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_374 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_373);
x_377 = l_Lean_Meta_isExprDefEq(x_375, x_373, x_10, x_11, x_12, x_13, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_unbox(x_378);
lean_dec(x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_17);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec(x_377);
x_381 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_373);
x_382 = l_Lean_Meta_trySynthInstance(x_373, x_381, x_10, x_11, x_12, x_13, x_380);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 1)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_373);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
lean_dec(x_383);
lean_inc(x_2);
x_386 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_308, x_2, x_309, x_310, x_311, x_385, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_384);
lean_dec(x_311);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_18 = x_387;
x_19 = x_388;
goto block_26;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_383);
x_389 = lean_ctor_get(x_382, 1);
lean_inc(x_389);
lean_dec(x_382);
x_390 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_391 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_390, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_389);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_373);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_395 = lean_box(0);
x_396 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_381, x_310, x_311, x_309, x_35, x_308, x_395, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_394);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_18 = x_397;
x_19 = x_398;
goto block_26;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_399 = lean_ctor_get(x_391, 1);
lean_inc(x_399);
lean_dec(x_391);
x_400 = l_Lean_indentExpr(x_373);
x_401 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_404 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
x_405 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_390, x_404, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_399);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_381, x_310, x_311, x_309, x_35, x_308, x_406, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_407);
lean_dec(x_406);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_18 = x_409;
x_19 = x_410;
goto block_26;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_373);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_411 = lean_ctor_get(x_382, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_382, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_413 = x_382;
} else {
 lean_dec_ref(x_382);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_373);
x_415 = lean_ctor_get(x_377, 1);
lean_inc(x_415);
lean_dec(x_377);
lean_inc(x_2);
x_416 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_308, x_2, x_309, x_310, x_311, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_415);
lean_dec(x_311);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_18 = x_417;
x_19 = x_418;
goto block_26;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_373);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_419 = lean_ctor_get(x_377, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_377, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_421 = x_377;
} else {
 lean_dec_ref(x_377);
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
lean_dec(x_373);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_423 = lean_ctor_get(x_374, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_374, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_425 = x_374;
} else {
 lean_dec_ref(x_374);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
default: 
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_312);
lean_dec(x_17);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_310);
lean_ctor_set(x_427, 1, x_311);
lean_ctor_set(x_29, 1, x_427);
lean_ctor_set(x_29, 0, x_309);
lean_ctor_set(x_27, 0, x_308);
lean_inc(x_2);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_2);
lean_ctor_set(x_428, 1, x_27);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_18 = x_429;
x_19 = x_14;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_430 = lean_ctor_get(x_29, 0);
lean_inc(x_430);
lean_dec(x_29);
x_431 = lean_ctor_get(x_30, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_30, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_433 = x_30;
} else {
 lean_dec_ref(x_30);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_32, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_32, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_32, 2);
lean_inc(x_436);
x_437 = lean_nat_dec_lt(x_435, x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_436);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_17);
if (lean_is_scalar(x_433)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_433;
}
lean_ctor_set(x_438, 0, x_431);
lean_ctor_set(x_438, 1, x_432);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_430);
lean_ctor_set(x_439, 1, x_438);
lean_ctor_set(x_28, 1, x_439);
lean_inc(x_2);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_2);
lean_ctor_set(x_440, 1, x_27);
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_18 = x_441;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_442 = x_32;
} else {
 lean_dec_ref(x_32);
 x_442 = lean_box(0);
}
x_443 = lean_array_fget(x_434, x_435);
x_444 = lean_unbox(x_443);
lean_dec(x_443);
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_nat_add(x_435, x_445);
lean_dec(x_435);
if (lean_is_scalar(x_442)) {
 x_447 = lean_alloc_ctor(0, 3, 0);
} else {
 x_447 = x_442;
}
lean_ctor_set(x_447, 0, x_434);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set(x_447, 2, x_436);
lean_inc(x_17);
x_448 = l_Lean_Expr_app___override(x_430, x_17);
lean_inc(x_17);
x_449 = lean_array_push(x_431, x_17);
x_450 = l_Lean_Expr_bindingBody_x21(x_432);
lean_dec(x_432);
x_451 = lean_box(x_444);
switch (lean_obj_tag(x_451)) {
case 1:
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_17);
x_452 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_453 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_452, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
lean_dec(x_453);
if (lean_is_scalar(x_433)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_433;
}
lean_ctor_set(x_455, 0, x_449);
lean_ctor_set(x_455, 1, x_450);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_448);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_28, 1, x_456);
lean_ctor_set(x_27, 0, x_447);
lean_inc(x_2);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_2);
lean_ctor_set(x_457, 1, x_27);
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_457);
x_18 = x_458;
x_19 = x_454;
goto block_26;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_433);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_459 = lean_ctor_get(x_453, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_453, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_461 = x_453;
} else {
 lean_dec_ref(x_453);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
case 2:
{
lean_object* x_463; uint8_t x_464; 
x_463 = lean_array_get_size(x_1);
x_464 = lean_nat_dec_lt(x_35, x_463);
lean_dec(x_463);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = l_Lean_Meta_Simp_instInhabitedResult;
x_466 = l___private_Init_Util_0__outOfBounds___rarg(x_465);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_466);
x_467 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_466, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_nat_add(x_35, x_445);
lean_dec(x_35);
x_471 = lean_ctor_get(x_466, 0);
lean_inc(x_471);
lean_dec(x_466);
lean_inc(x_468);
lean_inc(x_471);
x_472 = l_Lean_mkAppB(x_448, x_471, x_468);
x_473 = lean_array_push(x_449, x_471);
x_474 = lean_array_push(x_473, x_468);
x_475 = l_Lean_Expr_bindingBody_x21(x_450);
lean_dec(x_450);
x_476 = l_Lean_Expr_bindingBody_x21(x_475);
lean_dec(x_475);
if (lean_is_scalar(x_433)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_433;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_476);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_472);
lean_ctor_set(x_478, 1, x_477);
lean_ctor_set(x_28, 1, x_478);
lean_ctor_set(x_28, 0, x_470);
lean_ctor_set(x_27, 0, x_447);
lean_inc(x_2);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_2);
lean_ctor_set(x_479, 1, x_27);
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_479);
x_18 = x_480;
x_19 = x_469;
goto block_26;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_466);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_433);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_481 = lean_ctor_get(x_467, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_467, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_483 = x_467;
} else {
 lean_dec_ref(x_467);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_array_fget(x_1, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_485);
x_486 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_485, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_nat_add(x_35, x_445);
lean_dec(x_35);
x_490 = lean_ctor_get(x_485, 0);
lean_inc(x_490);
lean_dec(x_485);
lean_inc(x_487);
lean_inc(x_490);
x_491 = l_Lean_mkAppB(x_448, x_490, x_487);
x_492 = lean_array_push(x_449, x_490);
x_493 = lean_array_push(x_492, x_487);
x_494 = l_Lean_Expr_bindingBody_x21(x_450);
lean_dec(x_450);
x_495 = l_Lean_Expr_bindingBody_x21(x_494);
lean_dec(x_494);
if (lean_is_scalar(x_433)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_433;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_491);
lean_ctor_set(x_497, 1, x_496);
lean_ctor_set(x_28, 1, x_497);
lean_ctor_set(x_28, 0, x_489);
lean_ctor_set(x_27, 0, x_447);
lean_inc(x_2);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_2);
lean_ctor_set(x_498, 1, x_27);
x_499 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_499, 0, x_498);
x_18 = x_499;
x_19 = x_488;
goto block_26;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_485);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_433);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_500 = lean_ctor_get(x_486, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_486, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_502 = x_486;
} else {
 lean_dec_ref(x_486);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
}
case 4:
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_17);
x_504 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_505 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_504, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
if (lean_is_scalar(x_433)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_433;
}
lean_ctor_set(x_507, 0, x_449);
lean_ctor_set(x_507, 1, x_450);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_448);
lean_ctor_set(x_508, 1, x_507);
lean_ctor_set(x_28, 1, x_508);
lean_ctor_set(x_27, 0, x_447);
lean_inc(x_2);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_2);
lean_ctor_set(x_509, 1, x_27);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_18 = x_510;
x_19 = x_506;
goto block_26;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_433);
lean_free_object(x_28);
lean_dec(x_35);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_511 = lean_ctor_get(x_505, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_505, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_513 = x_505;
} else {
 lean_dec_ref(x_505);
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
case 5:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_433);
lean_free_object(x_28);
lean_free_object(x_27);
x_515 = l_Lean_Expr_bindingDomain_x21(x_450);
x_516 = lean_expr_instantiate_rev(x_515, x_449);
lean_dec(x_515);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_517 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_516);
x_520 = l_Lean_Meta_isExprDefEq(x_518, x_516, x_10, x_11, x_12, x_13, x_519);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; uint8_t x_522; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_unbox(x_521);
lean_dec(x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_17);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
lean_dec(x_520);
x_524 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_516);
x_525 = l_Lean_Meta_trySynthInstance(x_516, x_524, x_10, x_11, x_12, x_13, x_523);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 1)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_516);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
lean_dec(x_526);
lean_inc(x_2);
x_529 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_447, x_2, x_448, x_449, x_450, x_528, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_527);
lean_dec(x_450);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_18 = x_530;
x_19 = x_531;
goto block_26;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
lean_dec(x_526);
x_532 = lean_ctor_get(x_525, 1);
lean_inc(x_532);
lean_dec(x_525);
x_533 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_534 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_533, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_532);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_unbox(x_535);
lean_dec(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_516);
x_537 = lean_ctor_get(x_534, 1);
lean_inc(x_537);
lean_dec(x_534);
x_538 = lean_box(0);
x_539 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_524, x_449, x_450, x_448, x_35, x_447, x_538, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_537);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_18 = x_540;
x_19 = x_541;
goto block_26;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_542 = lean_ctor_get(x_534, 1);
lean_inc(x_542);
lean_dec(x_534);
x_543 = l_Lean_indentExpr(x_516);
x_544 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_545 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_547 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_533, x_547, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_542);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_524, x_449, x_450, x_448, x_35, x_447, x_549, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_550);
lean_dec(x_549);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_18 = x_552;
x_19 = x_553;
goto block_26;
}
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_516);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_554 = lean_ctor_get(x_525, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_525, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_556 = x_525;
} else {
 lean_dec_ref(x_525);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_516);
x_558 = lean_ctor_get(x_520, 1);
lean_inc(x_558);
lean_dec(x_520);
lean_inc(x_2);
x_559 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_35, x_447, x_2, x_448, x_449, x_450, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_558);
lean_dec(x_450);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_18 = x_560;
x_19 = x_561;
goto block_26;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_516);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_562 = lean_ctor_get(x_520, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_520, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_564 = x_520;
} else {
 lean_dec_ref(x_520);
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
lean_dec(x_516);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_566 = lean_ctor_get(x_517, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_517, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_568 = x_517;
} else {
 lean_dec_ref(x_517);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
default: 
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_451);
lean_dec(x_17);
if (lean_is_scalar(x_433)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_433;
}
lean_ctor_set(x_570, 0, x_449);
lean_ctor_set(x_570, 1, x_450);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_448);
lean_ctor_set(x_571, 1, x_570);
lean_ctor_set(x_28, 1, x_571);
lean_ctor_set(x_27, 0, x_447);
lean_inc(x_2);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_2);
lean_ctor_set(x_572, 1, x_27);
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_572);
x_18 = x_573;
x_19 = x_14;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_574 = lean_ctor_get(x_28, 0);
lean_inc(x_574);
lean_dec(x_28);
x_575 = lean_ctor_get(x_29, 0);
lean_inc(x_575);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_576 = x_29;
} else {
 lean_dec_ref(x_29);
 x_576 = lean_box(0);
}
x_577 = lean_ctor_get(x_30, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_30, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_579 = x_30;
} else {
 lean_dec_ref(x_30);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_32, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_32, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_32, 2);
lean_inc(x_582);
x_583 = lean_nat_dec_lt(x_581, x_582);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_580);
lean_dec(x_17);
if (lean_is_scalar(x_579)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_579;
}
lean_ctor_set(x_584, 0, x_577);
lean_ctor_set(x_584, 1, x_578);
if (lean_is_scalar(x_576)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_576;
}
lean_ctor_set(x_585, 0, x_575);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_574);
lean_ctor_set(x_586, 1, x_585);
lean_ctor_set(x_27, 1, x_586);
lean_inc(x_2);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_2);
lean_ctor_set(x_587, 1, x_27);
x_588 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_588, 0, x_587);
x_18 = x_588;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_589 = x_32;
} else {
 lean_dec_ref(x_32);
 x_589 = lean_box(0);
}
x_590 = lean_array_fget(x_580, x_581);
x_591 = lean_unbox(x_590);
lean_dec(x_590);
x_592 = lean_unsigned_to_nat(1u);
x_593 = lean_nat_add(x_581, x_592);
lean_dec(x_581);
if (lean_is_scalar(x_589)) {
 x_594 = lean_alloc_ctor(0, 3, 0);
} else {
 x_594 = x_589;
}
lean_ctor_set(x_594, 0, x_580);
lean_ctor_set(x_594, 1, x_593);
lean_ctor_set(x_594, 2, x_582);
lean_inc(x_17);
x_595 = l_Lean_Expr_app___override(x_575, x_17);
lean_inc(x_17);
x_596 = lean_array_push(x_577, x_17);
x_597 = l_Lean_Expr_bindingBody_x21(x_578);
lean_dec(x_578);
x_598 = lean_box(x_591);
switch (lean_obj_tag(x_598)) {
case 1:
{
lean_object* x_599; lean_object* x_600; 
lean_dec(x_17);
x_599 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_600 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_599, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
lean_dec(x_600);
if (lean_is_scalar(x_579)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_579;
}
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_597);
if (lean_is_scalar(x_576)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_576;
}
lean_ctor_set(x_603, 0, x_595);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_574);
lean_ctor_set(x_604, 1, x_603);
lean_ctor_set(x_27, 1, x_604);
lean_ctor_set(x_27, 0, x_594);
lean_inc(x_2);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_2);
lean_ctor_set(x_605, 1, x_27);
x_606 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_606, 0, x_605);
x_18 = x_606;
x_19 = x_601;
goto block_26;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_579);
lean_dec(x_576);
lean_dec(x_574);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_607 = lean_ctor_get(x_600, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_600, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_609 = x_600;
} else {
 lean_dec_ref(x_600);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_608);
return x_610;
}
}
case 2:
{
lean_object* x_611; uint8_t x_612; 
x_611 = lean_array_get_size(x_1);
x_612 = lean_nat_dec_lt(x_574, x_611);
lean_dec(x_611);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = l_Lean_Meta_Simp_instInhabitedResult;
x_614 = l___private_Init_Util_0__outOfBounds___rarg(x_613);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_614);
x_615 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_614, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_nat_add(x_574, x_592);
lean_dec(x_574);
x_619 = lean_ctor_get(x_614, 0);
lean_inc(x_619);
lean_dec(x_614);
lean_inc(x_616);
lean_inc(x_619);
x_620 = l_Lean_mkAppB(x_595, x_619, x_616);
x_621 = lean_array_push(x_596, x_619);
x_622 = lean_array_push(x_621, x_616);
x_623 = l_Lean_Expr_bindingBody_x21(x_597);
lean_dec(x_597);
x_624 = l_Lean_Expr_bindingBody_x21(x_623);
lean_dec(x_623);
if (lean_is_scalar(x_579)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_579;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_624);
if (lean_is_scalar(x_576)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_576;
}
lean_ctor_set(x_626, 0, x_620);
lean_ctor_set(x_626, 1, x_625);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_618);
lean_ctor_set(x_627, 1, x_626);
lean_ctor_set(x_27, 1, x_627);
lean_ctor_set(x_27, 0, x_594);
lean_inc(x_2);
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_2);
lean_ctor_set(x_628, 1, x_27);
x_629 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_629, 0, x_628);
x_18 = x_629;
x_19 = x_617;
goto block_26;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_614);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_579);
lean_dec(x_576);
lean_dec(x_574);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_630 = lean_ctor_get(x_615, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_615, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_632 = x_615;
} else {
 lean_dec_ref(x_615);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_630);
lean_ctor_set(x_633, 1, x_631);
return x_633;
}
}
else
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_array_fget(x_1, x_574);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_634);
x_635 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_634, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_nat_add(x_574, x_592);
lean_dec(x_574);
x_639 = lean_ctor_get(x_634, 0);
lean_inc(x_639);
lean_dec(x_634);
lean_inc(x_636);
lean_inc(x_639);
x_640 = l_Lean_mkAppB(x_595, x_639, x_636);
x_641 = lean_array_push(x_596, x_639);
x_642 = lean_array_push(x_641, x_636);
x_643 = l_Lean_Expr_bindingBody_x21(x_597);
lean_dec(x_597);
x_644 = l_Lean_Expr_bindingBody_x21(x_643);
lean_dec(x_643);
if (lean_is_scalar(x_579)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_579;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_644);
if (lean_is_scalar(x_576)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_576;
}
lean_ctor_set(x_646, 0, x_640);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_638);
lean_ctor_set(x_647, 1, x_646);
lean_ctor_set(x_27, 1, x_647);
lean_ctor_set(x_27, 0, x_594);
lean_inc(x_2);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_2);
lean_ctor_set(x_648, 1, x_27);
x_649 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_649, 0, x_648);
x_18 = x_649;
x_19 = x_637;
goto block_26;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_634);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_579);
lean_dec(x_576);
lean_dec(x_574);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_650 = lean_ctor_get(x_635, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_635, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_652 = x_635;
} else {
 lean_dec_ref(x_635);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
}
case 4:
{
lean_object* x_654; lean_object* x_655; 
lean_dec(x_17);
x_654 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_655 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_654, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
lean_dec(x_655);
if (lean_is_scalar(x_579)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_579;
}
lean_ctor_set(x_657, 0, x_596);
lean_ctor_set(x_657, 1, x_597);
if (lean_is_scalar(x_576)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_576;
}
lean_ctor_set(x_658, 0, x_595);
lean_ctor_set(x_658, 1, x_657);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_574);
lean_ctor_set(x_659, 1, x_658);
lean_ctor_set(x_27, 1, x_659);
lean_ctor_set(x_27, 0, x_594);
lean_inc(x_2);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_2);
lean_ctor_set(x_660, 1, x_27);
x_661 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_661, 0, x_660);
x_18 = x_661;
x_19 = x_656;
goto block_26;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_579);
lean_dec(x_576);
lean_dec(x_574);
lean_free_object(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_662 = lean_ctor_get(x_655, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_655, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_664 = x_655;
} else {
 lean_dec_ref(x_655);
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
case 5:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_579);
lean_dec(x_576);
lean_free_object(x_27);
x_666 = l_Lean_Expr_bindingDomain_x21(x_597);
x_667 = lean_expr_instantiate_rev(x_666, x_596);
lean_dec(x_666);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_668 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_667);
x_671 = l_Lean_Meta_isExprDefEq(x_669, x_667, x_10, x_11, x_12, x_13, x_670);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; uint8_t x_673; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_unbox(x_672);
lean_dec(x_672);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_17);
x_674 = lean_ctor_get(x_671, 1);
lean_inc(x_674);
lean_dec(x_671);
x_675 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_667);
x_676 = l_Lean_Meta_trySynthInstance(x_667, x_675, x_10, x_11, x_12, x_13, x_674);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
if (lean_obj_tag(x_677) == 1)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_667);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = lean_ctor_get(x_677, 0);
lean_inc(x_679);
lean_dec(x_677);
lean_inc(x_2);
x_680 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_574, x_594, x_2, x_595, x_596, x_597, x_679, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_678);
lean_dec(x_597);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_18 = x_681;
x_19 = x_682;
goto block_26;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
lean_dec(x_677);
x_683 = lean_ctor_get(x_676, 1);
lean_inc(x_683);
lean_dec(x_676);
x_684 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_685 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_684, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_683);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_unbox(x_686);
lean_dec(x_686);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_667);
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
lean_dec(x_685);
x_689 = lean_box(0);
x_690 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_675, x_596, x_597, x_595, x_574, x_594, x_689, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_688);
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_18 = x_691;
x_19 = x_692;
goto block_26;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_693 = lean_ctor_get(x_685, 1);
lean_inc(x_693);
lean_dec(x_685);
x_694 = l_Lean_indentExpr(x_667);
x_695 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_696 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_694);
x_697 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_698 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
x_699 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_684, x_698, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_693);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_675, x_596, x_597, x_595, x_574, x_594, x_700, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_701);
lean_dec(x_700);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_18 = x_703;
x_19 = x_704;
goto block_26;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_667);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_574);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_705 = lean_ctor_get(x_676, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_676, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_707 = x_676;
} else {
 lean_dec_ref(x_676);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_705);
lean_ctor_set(x_708, 1, x_706);
return x_708;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_667);
x_709 = lean_ctor_get(x_671, 1);
lean_inc(x_709);
lean_dec(x_671);
lean_inc(x_2);
x_710 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_574, x_594, x_2, x_595, x_596, x_597, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_709);
lean_dec(x_597);
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
lean_dec(x_710);
x_18 = x_711;
x_19 = x_712;
goto block_26;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_667);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_574);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_713 = lean_ctor_get(x_671, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_671, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_715 = x_671;
} else {
 lean_dec_ref(x_671);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_667);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_574);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_717 = lean_ctor_get(x_668, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_668, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_719 = x_668;
} else {
 lean_dec_ref(x_668);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_717);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
default: 
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_598);
lean_dec(x_17);
if (lean_is_scalar(x_579)) {
 x_721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_721 = x_579;
}
lean_ctor_set(x_721, 0, x_596);
lean_ctor_set(x_721, 1, x_597);
if (lean_is_scalar(x_576)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_576;
}
lean_ctor_set(x_722, 0, x_595);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_574);
lean_ctor_set(x_723, 1, x_722);
lean_ctor_set(x_27, 1, x_723);
lean_ctor_set(x_27, 0, x_594);
lean_inc(x_2);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_2);
lean_ctor_set(x_724, 1, x_27);
x_725 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_725, 0, x_724);
x_18 = x_725;
x_19 = x_14;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; 
x_726 = lean_ctor_get(x_27, 0);
lean_inc(x_726);
lean_dec(x_27);
x_727 = lean_ctor_get(x_28, 0);
lean_inc(x_727);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_728 = x_28;
} else {
 lean_dec_ref(x_28);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_29, 0);
lean_inc(x_729);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_730 = x_29;
} else {
 lean_dec_ref(x_29);
 x_730 = lean_box(0);
}
x_731 = lean_ctor_get(x_30, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_30, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_733 = x_30;
} else {
 lean_dec_ref(x_30);
 x_733 = lean_box(0);
}
x_734 = lean_ctor_get(x_726, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_726, 1);
lean_inc(x_735);
x_736 = lean_ctor_get(x_726, 2);
lean_inc(x_736);
x_737 = lean_nat_dec_lt(x_735, x_736);
if (x_737 == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_734);
lean_dec(x_17);
if (lean_is_scalar(x_733)) {
 x_738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_738 = x_733;
}
lean_ctor_set(x_738, 0, x_731);
lean_ctor_set(x_738, 1, x_732);
if (lean_is_scalar(x_730)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_730;
}
lean_ctor_set(x_739, 0, x_729);
lean_ctor_set(x_739, 1, x_738);
if (lean_is_scalar(x_728)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_728;
}
lean_ctor_set(x_740, 0, x_727);
lean_ctor_set(x_740, 1, x_739);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_726);
lean_ctor_set(x_741, 1, x_740);
lean_inc(x_2);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_2);
lean_ctor_set(x_742, 1, x_741);
x_743 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_743, 0, x_742);
x_18 = x_743;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_744; lean_object* x_745; uint8_t x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 lean_ctor_release(x_726, 2);
 x_744 = x_726;
} else {
 lean_dec_ref(x_726);
 x_744 = lean_box(0);
}
x_745 = lean_array_fget(x_734, x_735);
x_746 = lean_unbox(x_745);
lean_dec(x_745);
x_747 = lean_unsigned_to_nat(1u);
x_748 = lean_nat_add(x_735, x_747);
lean_dec(x_735);
if (lean_is_scalar(x_744)) {
 x_749 = lean_alloc_ctor(0, 3, 0);
} else {
 x_749 = x_744;
}
lean_ctor_set(x_749, 0, x_734);
lean_ctor_set(x_749, 1, x_748);
lean_ctor_set(x_749, 2, x_736);
lean_inc(x_17);
x_750 = l_Lean_Expr_app___override(x_729, x_17);
lean_inc(x_17);
x_751 = lean_array_push(x_731, x_17);
x_752 = l_Lean_Expr_bindingBody_x21(x_732);
lean_dec(x_732);
x_753 = lean_box(x_746);
switch (lean_obj_tag(x_753)) {
case 1:
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_17);
x_754 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_755 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_754, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_756 = lean_ctor_get(x_755, 1);
lean_inc(x_756);
lean_dec(x_755);
if (lean_is_scalar(x_733)) {
 x_757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_757 = x_733;
}
lean_ctor_set(x_757, 0, x_751);
lean_ctor_set(x_757, 1, x_752);
if (lean_is_scalar(x_730)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_730;
}
lean_ctor_set(x_758, 0, x_750);
lean_ctor_set(x_758, 1, x_757);
if (lean_is_scalar(x_728)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_728;
}
lean_ctor_set(x_759, 0, x_727);
lean_ctor_set(x_759, 1, x_758);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_749);
lean_ctor_set(x_760, 1, x_759);
lean_inc(x_2);
x_761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_761, 0, x_2);
lean_ctor_set(x_761, 1, x_760);
x_762 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_762, 0, x_761);
x_18 = x_762;
x_19 = x_756;
goto block_26;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_727);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_763 = lean_ctor_get(x_755, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_755, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_765 = x_755;
} else {
 lean_dec_ref(x_755);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
case 2:
{
lean_object* x_767; uint8_t x_768; 
x_767 = lean_array_get_size(x_1);
x_768 = lean_nat_dec_lt(x_727, x_767);
lean_dec(x_767);
if (x_768 == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = l_Lean_Meta_Simp_instInhabitedResult;
x_770 = l___private_Init_Util_0__outOfBounds___rarg(x_769);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_770);
x_771 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_770, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_nat_add(x_727, x_747);
lean_dec(x_727);
x_775 = lean_ctor_get(x_770, 0);
lean_inc(x_775);
lean_dec(x_770);
lean_inc(x_772);
lean_inc(x_775);
x_776 = l_Lean_mkAppB(x_750, x_775, x_772);
x_777 = lean_array_push(x_751, x_775);
x_778 = lean_array_push(x_777, x_772);
x_779 = l_Lean_Expr_bindingBody_x21(x_752);
lean_dec(x_752);
x_780 = l_Lean_Expr_bindingBody_x21(x_779);
lean_dec(x_779);
if (lean_is_scalar(x_733)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_733;
}
lean_ctor_set(x_781, 0, x_778);
lean_ctor_set(x_781, 1, x_780);
if (lean_is_scalar(x_730)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_730;
}
lean_ctor_set(x_782, 0, x_776);
lean_ctor_set(x_782, 1, x_781);
if (lean_is_scalar(x_728)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_728;
}
lean_ctor_set(x_783, 0, x_774);
lean_ctor_set(x_783, 1, x_782);
x_784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_784, 0, x_749);
lean_ctor_set(x_784, 1, x_783);
lean_inc(x_2);
x_785 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_785, 0, x_2);
lean_ctor_set(x_785, 1, x_784);
x_786 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_786, 0, x_785);
x_18 = x_786;
x_19 = x_773;
goto block_26;
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_770);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_727);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_787 = lean_ctor_get(x_771, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_771, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_789 = x_771;
} else {
 lean_dec_ref(x_771);
 x_789 = lean_box(0);
}
if (lean_is_scalar(x_789)) {
 x_790 = lean_alloc_ctor(1, 2, 0);
} else {
 x_790 = x_789;
}
lean_ctor_set(x_790, 0, x_787);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; 
x_791 = lean_array_fget(x_1, x_727);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_791);
x_792 = l_Lean_Meta_Simp_Result_getProof_x27(x_17, x_791, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_nat_add(x_727, x_747);
lean_dec(x_727);
x_796 = lean_ctor_get(x_791, 0);
lean_inc(x_796);
lean_dec(x_791);
lean_inc(x_793);
lean_inc(x_796);
x_797 = l_Lean_mkAppB(x_750, x_796, x_793);
x_798 = lean_array_push(x_751, x_796);
x_799 = lean_array_push(x_798, x_793);
x_800 = l_Lean_Expr_bindingBody_x21(x_752);
lean_dec(x_752);
x_801 = l_Lean_Expr_bindingBody_x21(x_800);
lean_dec(x_800);
if (lean_is_scalar(x_733)) {
 x_802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_802 = x_733;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_801);
if (lean_is_scalar(x_730)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_730;
}
lean_ctor_set(x_803, 0, x_797);
lean_ctor_set(x_803, 1, x_802);
if (lean_is_scalar(x_728)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_728;
}
lean_ctor_set(x_804, 0, x_795);
lean_ctor_set(x_804, 1, x_803);
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_749);
lean_ctor_set(x_805, 1, x_804);
lean_inc(x_2);
x_806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_806, 0, x_2);
lean_ctor_set(x_806, 1, x_805);
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_806);
x_18 = x_807;
x_19 = x_794;
goto block_26;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_791);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_727);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_808 = lean_ctor_get(x_792, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_792, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_810 = x_792;
} else {
 lean_dec_ref(x_792);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_808);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
}
case 4:
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_17);
x_812 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_813 = l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__3(x_812, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
lean_dec(x_813);
if (lean_is_scalar(x_733)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_733;
}
lean_ctor_set(x_815, 0, x_751);
lean_ctor_set(x_815, 1, x_752);
if (lean_is_scalar(x_730)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_730;
}
lean_ctor_set(x_816, 0, x_750);
lean_ctor_set(x_816, 1, x_815);
if (lean_is_scalar(x_728)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_728;
}
lean_ctor_set(x_817, 0, x_727);
lean_ctor_set(x_817, 1, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_749);
lean_ctor_set(x_818, 1, x_817);
lean_inc(x_2);
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_2);
lean_ctor_set(x_819, 1, x_818);
x_820 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_820, 0, x_819);
x_18 = x_820;
x_19 = x_814;
goto block_26;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_728);
lean_dec(x_727);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_821 = lean_ctor_get(x_813, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_813, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_823 = x_813;
} else {
 lean_dec_ref(x_813);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(1, 2, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_821);
lean_ctor_set(x_824, 1, x_822);
return x_824;
}
}
case 5:
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
lean_dec(x_733);
lean_dec(x_730);
lean_dec(x_728);
x_825 = l_Lean_Expr_bindingDomain_x21(x_752);
x_826 = lean_expr_instantiate_rev(x_825, x_751);
lean_dec(x_825);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_827 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_826);
x_830 = l_Lean_Meta_isExprDefEq(x_828, x_826, x_10, x_11, x_12, x_13, x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; uint8_t x_832; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_unbox(x_831);
lean_dec(x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_17);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_dec(x_830);
x_834 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_826);
x_835 = l_Lean_Meta_trySynthInstance(x_826, x_834, x_10, x_11, x_12, x_13, x_833);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
if (lean_obj_tag(x_836) == 1)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_826);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_838 = lean_ctor_get(x_836, 0);
lean_inc(x_838);
lean_dec(x_836);
lean_inc(x_2);
x_839 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_727, x_749, x_2, x_750, x_751, x_752, x_838, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_837);
lean_dec(x_752);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_18 = x_840;
x_19 = x_841;
goto block_26;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; 
lean_dec(x_836);
x_842 = lean_ctor_get(x_835, 1);
lean_inc(x_842);
lean_dec(x_835);
x_843 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__3;
x_844 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_843, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_842);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_unbox(x_845);
lean_dec(x_845);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_826);
x_847 = lean_ctor_get(x_844, 1);
lean_inc(x_847);
lean_dec(x_844);
x_848 = lean_box(0);
x_849 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_834, x_751, x_752, x_750, x_727, x_749, x_848, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_847);
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec(x_849);
x_18 = x_850;
x_19 = x_851;
goto block_26;
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_852 = lean_ctor_get(x_844, 1);
lean_inc(x_852);
lean_dec(x_844);
x_853 = l_Lean_indentExpr(x_826);
x_854 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___closed__5;
x_855 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_855, 0, x_854);
lean_ctor_set(x_855, 1, x_853);
x_856 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__16;
x_857 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_858 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_843, x_857, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_852);
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_834, x_751, x_752, x_750, x_727, x_749, x_859, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_860);
lean_dec(x_859);
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_18 = x_862;
x_19 = x_863;
goto block_26;
}
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_826);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_727);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_864 = lean_ctor_get(x_835, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_835, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 lean_ctor_release(x_835, 1);
 x_866 = x_835;
} else {
 lean_dec_ref(x_835);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_865);
return x_867;
}
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_826);
x_868 = lean_ctor_get(x_830, 1);
lean_inc(x_868);
lean_dec(x_830);
lean_inc(x_2);
x_869 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_727, x_749, x_2, x_750, x_751, x_752, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_868);
lean_dec(x_752);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_18 = x_870;
x_19 = x_871;
goto block_26;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_826);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_727);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_872 = lean_ctor_get(x_830, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_830, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_874 = x_830;
} else {
 lean_dec_ref(x_830);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_826);
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_727);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_876 = lean_ctor_get(x_827, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_827, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_878 = x_827;
} else {
 lean_dec_ref(x_827);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
default: 
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_753);
lean_dec(x_17);
if (lean_is_scalar(x_733)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_733;
}
lean_ctor_set(x_880, 0, x_751);
lean_ctor_set(x_880, 1, x_752);
if (lean_is_scalar(x_730)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_730;
}
lean_ctor_set(x_881, 0, x_750);
lean_ctor_set(x_881, 1, x_880);
if (lean_is_scalar(x_728)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_728;
}
lean_ctor_set(x_882, 0, x_727);
lean_ctor_set(x_882, 1, x_881);
x_883 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_883, 0, x_749);
lean_ctor_set(x_883, 1, x_882);
lean_inc(x_2);
x_884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_884, 0, x_2);
lean_ctor_set(x_884, 1, x_883);
x_885 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_885, 0, x_884);
x_18 = x_885;
x_19 = x_14;
goto block_26;
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
x_3 = l_instInhabited___rarg(x_2, x_1);
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
uint32_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_13 = 0;
x_14 = 1;
x_15 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set_uint32(x_15, sizeof(void*)*2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 4, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = 0;
x_20 = 1;
x_21 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set_uint32(x_21, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 4, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
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
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(474u);
x_4 = lean_unsigned_to_nat(61u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_16 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4(x_4, x_21, x_5, x_6, x_7, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__2(x_38, x_37, x_8, x_21, x_36, x_9, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_35);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_28, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
lean_ctor_set(x_28, 0, x_43);
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
lean_dec(x_34);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_dec(x_12);
if (x_8 == 0)
{
if (x_9 == 0)
{
lean_object* x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_mkAppN(x_10, x_11);
x_22 = lean_box(0);
x_23 = 0;
x_24 = 1;
x_25 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint32(x_25, sizeof(void*)*2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_10);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
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
x_1 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
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
x_1 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
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
lean_dec(x_4);
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
lean_inc(x_20);
lean_inc(x_2);
x_21 = l_Lean_Meta_getFunInfoNArgs(x_2, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Lean_Meta_Simp_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
x_30 = l_Array_toSubarray___rarg(x_28, x_13, x_29);
x_31 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__5___closed__5;
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_34 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2(x_22, x_24, x_26, x_19, x_33, x_34, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_26);
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
lean_dec(x_30);
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
lean_object* x_45; lean_object* x_46; uint32_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = 0;
x_48 = 1;
x_49 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set_uint32(x_49, sizeof(void*)*2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 4, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_35, 0, x_50);
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; uint32_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_box(0);
x_53 = 0;
x_54 = 1;
x_55 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set_uint32(x_55, sizeof(void*)*2, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 4, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_1);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec(x_35);
x_59 = lean_ctor_get(x_37, 0);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_ctor_get(x_38, 0);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_ctor_get(x_39, 0);
lean_inc(x_61);
lean_dec(x_39);
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
x_64 = lean_box(0);
x_65 = lean_unbox(x_62);
lean_dec(x_62);
x_66 = lean_unbox(x_61);
lean_dec(x_61);
x_67 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_3, x_63, x_30, x_59, x_19, x_33, x_34, x_65, x_66, x_2, x_60, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
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
x_68 = !lean_is_exclusive(x_35);
if (x_68 == 0)
{
return x_35;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_20);
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
x_72 = !lean_is_exclusive(x_21);
if (x_72 == 0)
{
return x_21;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
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
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3(x_1, x_19, x_3, x_4, x_5, x_20, x_21, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
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
_start:
{
size_t x_19; size_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_19, x_20, x_21, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_23;
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
x_21 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_22 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_23 = lean_unbox(x_8);
lean_dec(x_8);
x_24 = lean_unbox(x_9);
lean_dec(x_9);
x_25 = l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_21, x_22, x_23, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_25;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getDtConfig___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getDtConfig___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_2);
lean_ctor_set_uint8(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_getDtConfig___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getDtConfig___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_getDtConfig___closed__2;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_getDtConfig___closed__3;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Meta_simpDtConfig;
return x_8;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = lean_box(0);
x_12 = 0;
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 4, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_array_get_size(x_2);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_19, x_20, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_mkAppN(x_24, x_2);
lean_ctor_set(x_8, 0, x_23);
x_26 = 0;
x_27 = 1;
x_28 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_8);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 4, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_mkAppN(x_31, x_2);
lean_ctor_set(x_8, 0, x_29);
x_33 = 0;
x_34 = 1;
x_35 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_8);
lean_ctor_set_uint32(x_35, sizeof(void*)*2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 4, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_array_get_size(x_2);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_Result_addExtraArgs___spec__1(x_2, x_43, x_44, x_41, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
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
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l_Lean_mkAppN(x_49, x_2);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_52 = 0;
x_53 = 1;
x_54 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set_uint32(x_54, sizeof(void*)*2, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 4, x_53);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_47);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
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
lean_dec(x_2);
x_56 = l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1;
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
lean_dec(x_2);
x_82 = l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin, lean_io_mk_world());
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
l_Lean_Meta_Simp_Result_proof_x3f___default = _init_l_Lean_Meta_Simp_Result_proof_x3f___default();
lean_mark_persistent(l_Lean_Meta_Simp_Result_proof_x3f___default);
l_Lean_Meta_Simp_Result_dischargeDepth___default = _init_l_Lean_Meta_Simp_Result_dischargeDepth___default();
l_Lean_Meta_Simp_Result_cache___default = _init_l_Lean_Meta_Simp_Result_cache___default();
l_Lean_Meta_Simp_instInhabitedResult___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__1);
l_Lean_Meta_Simp_instInhabitedResult___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2();
l_Lean_Meta_Simp_instInhabitedResult___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__3);
l_Lean_Meta_Simp_instInhabitedResult = _init_l_Lean_Meta_Simp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult);
l_Lean_Meta_Simp_Context_config___default___closed__1 = _init_l_Lean_Meta_Simp_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_config___default___closed__1);
l_Lean_Meta_Simp_Context_config___default = _init_l_Lean_Meta_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_config___default);
l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1 = _init_l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1);
l_Lean_Meta_Simp_Context_simpTheorems___default = _init_l_Lean_Meta_Simp_Context_simpTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_simpTheorems___default);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5);
l_Lean_Meta_Simp_Context_congrTheorems___default = _init_l_Lean_Meta_Simp_Context_congrTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default);
l_Lean_Meta_Simp_Context_parent_x3f___default = _init_l_Lean_Meta_Simp_Context_parent_x3f___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_parent_x3f___default);
l_Lean_Meta_Simp_Context_dischargeDepth___default = _init_l_Lean_Meta_Simp_Context_dischargeDepth___default();
l_Lean_Meta_Simp_instInhabitedContext___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__1);
l_Lean_Meta_Simp_instInhabitedContext___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__2);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2();
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__3);
l_Lean_Meta_Simp_State_cache___default = _init_l_Lean_Meta_Simp_State_cache___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_cache___default);
l_Lean_Meta_Simp_State_congrCache___default = _init_l_Lean_Meta_Simp_State_congrCache___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_congrCache___default);
l_Lean_Meta_Simp_State_usedTheorems___default = _init_l_Lean_Meta_Simp_State_usedTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_usedTheorems___default);
l_Lean_Meta_Simp_State_numSteps___default = _init_l_Lean_Meta_Simp_State_numSteps___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_numSteps___default);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed();
l_Lean_Meta_Simp_instInhabitedStep___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep___closed__1);
l_Lean_Meta_Simp_instInhabitedStep = _init_l_Lean_Meta_Simp_instInhabitedStep();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep);
l_Lean_Meta_Simp_SimprocOLeanEntry_post___default = _init_l_Lean_Meta_Simp_SimprocOLeanEntry_post___default();
l_Lean_Meta_Simp_SimprocOLeanEntry_keys___default = _init_l_Lean_Meta_Simp_SimprocOLeanEntry_keys___default();
lean_mark_persistent(l_Lean_Meta_Simp_SimprocOLeanEntry_keys___default);
l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry = _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry);
l_Lean_Meta_Simp_Simprocs_pre___default___closed__1 = _init_l_Lean_Meta_Simp_Simprocs_pre___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Simprocs_pre___default___closed__1);
l_Lean_Meta_Simp_Simprocs_pre___default = _init_l_Lean_Meta_Simp_Simprocs_pre___default();
lean_mark_persistent(l_Lean_Meta_Simp_Simprocs_pre___default);
l_Lean_Meta_Simp_Simprocs_post___default = _init_l_Lean_Meta_Simp_Simprocs_post___default();
lean_mark_persistent(l_Lean_Meta_Simp_Simprocs_post___default);
l_Lean_Meta_Simp_Simprocs_simprocNames___default = _init_l_Lean_Meta_Simp_Simprocs_simprocNames___default();
lean_mark_persistent(l_Lean_Meta_Simp_Simprocs_simprocNames___default);
l_Lean_Meta_Simp_Simprocs_erased___default = _init_l_Lean_Meta_Simp_Simprocs_erased___default();
lean_mark_persistent(l_Lean_Meta_Simp_Simprocs_erased___default);
l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs___closed__1);
l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs___closed__2);
l_Lean_Meta_Simp_instInhabitedSimprocs = _init_l_Lean_Meta_Simp_instInhabitedSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs);
l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1 = _init_l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Methods_pre___default___rarg___closed__1);
l_Lean_Meta_Simp_instInhabitedMethods___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__1);
l_Lean_Meta_Simp_instInhabitedMethods___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__2);
l_Lean_Meta_Simp_instInhabitedMethods___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__3);
l_Lean_Meta_Simp_instInhabitedMethods = _init_l_Lean_Meta_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods);
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
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_congrArgs___spec__3___closed__22);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__1);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__2);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__3);
l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4 = _init_l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_tryAutoCongrTheorem_x3f___spec__2___lambda__3___closed__4);
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
l_Lean_Meta_Simp_getDtConfig___closed__1 = _init_l_Lean_Meta_Simp_getDtConfig___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_getDtConfig___closed__1);
l_Lean_Meta_Simp_getDtConfig___closed__2 = _init_l_Lean_Meta_Simp_getDtConfig___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_getDtConfig___closed__2);
l_Lean_Meta_Simp_getDtConfig___closed__3 = _init_l_Lean_Meta_Simp_getDtConfig___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_getDtConfig___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
