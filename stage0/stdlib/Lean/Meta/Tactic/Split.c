// Lean compiler output
// Module: Lean.Meta.Tactic.Split
// Imports: Lean.Meta.Match.MatcherApp.Basic Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.SplitIf Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Generalize
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
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__1;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__8;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lambda__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__5;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___boxed(lean_object**);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3;
lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4;
extern lean_object* l_Lean_casesOnSuffix;
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__10;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__5;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__2;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed(lean_object**);
static lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1___boxed(lean_object**);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Split_isDiscrGenException___closed__1;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__4;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__7;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1;
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2;
static lean_object* l_Lean_Meta_Split_splitMatch___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15;
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg(lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lambda__1___closed__5;
lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920_(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__6;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___boxed(lean_object**);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__3;
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13;
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2;
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatchEqns_size(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4;
static lean_object* l_Lean_Meta_Split_simpMatch___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lambda__1___closed__2;
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_getSimpMatchContext___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_findSplit_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2;
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__8;
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
static uint64_t l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_exprDependsOn___at___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__1;
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1;
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_hasForwardDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1;
static lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1;
static lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11;
uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_getSimpMatchContext___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Split_isDiscrGenException(lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_discrGenExId;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_isDiscrGenException___boxed(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6;
static lean_object* l_Lean_Meta_Split_simpMatch___closed__12;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__2;
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2;
static lean_object* _init_l_Lean_Meta_Split_getSimpMatchContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 19, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Split_getSimpMatchContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_Split_getSimpMatchContext___closed__1;
x_10 = l_Lean_Meta_Split_getSimpMatchContext___closed__2;
x_11 = l_Lean_Meta_Simp_mkContext(x_9, x_10, x_7, x_1, x_2, x_3, x_4, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Split_getSimpMatchContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_Meta_isMatcherAppCore(x_13, x_1);
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
x_19 = l_Lean_Meta_isMatcherAppCore(x_18, x_1);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_getAppFn(x_1);
x_12 = l_Lean_Expr_constName_x21(x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_simpMatchCore(x_12, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_33);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_31;
 lean_ctor_set_tag(x_35, 0);
}
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch_pre___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Split_simpMatch_pre___lambda__1(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at_Lean_Meta_Split_simpMatch_pre___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Split_simpMatch_pre___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Split_simpMatch___closed__5;
x_3 = l_Lean_Meta_Split_simpMatch___closed__4;
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
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__2;
x_2 = l_Lean_Meta_Split_simpMatch___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__3;
x_2 = l_Lean_Meta_Split_simpMatch___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch_pre), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lambda__2___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lambda__3___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_Meta_SplitIf_mkDischarge_x3f(x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Split_getSimpMatchContext(x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Split_simpMatch___closed__9;
x_15 = l_Lean_Meta_Split_simpMatch___closed__10;
x_16 = l_Lean_Meta_Split_simpMatch___closed__11;
x_17 = l_Lean_Meta_Split_simpMatch___closed__12;
x_18 = 1;
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_9);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_18);
x_20 = l_Lean_Meta_Split_simpMatch___closed__8;
x_21 = l_Lean_Meta_Simp_main(x_1, x_12, x_20, x_19, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_13 = l_Lean_Meta_Split_simpMatch(x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_applySimpResultToTarget(x_1, x_11, x_14, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_11);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatchTarget___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_15 = l_Lean_Meta_reduceRecMatcher_x3f(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Meta_isRflTheorem(x_2, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_2);
x_22 = l_Lean_Expr_const___override(x_2, x_21);
x_23 = 1;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_24);
x_26 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_27 = lean_unsigned_to_nat(1000u);
x_28 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 1, x_24);
x_29 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 2, x_29);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
uint64_t x_33; uint8_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_34 = 2;
lean_ctor_set_uint8(x_31, 9, x_34);
x_35 = 2;
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_shift_left(x_36, x_35);
x_38 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2;
x_39 = lean_uint64_lor(x_37, x_38);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_39);
x_40 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_40, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
lean_ctor_set_tag(x_41, 0);
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_40, 0, x_52);
return x_40;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_55 = x_41;
} else {
 lean_dec_ref(x_41);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
uint8_t x_58; 
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
uint64_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; lean_object* x_87; 
x_62 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_63 = lean_ctor_get_uint8(x_31, 0);
x_64 = lean_ctor_get_uint8(x_31, 1);
x_65 = lean_ctor_get_uint8(x_31, 2);
x_66 = lean_ctor_get_uint8(x_31, 3);
x_67 = lean_ctor_get_uint8(x_31, 4);
x_68 = lean_ctor_get_uint8(x_31, 5);
x_69 = lean_ctor_get_uint8(x_31, 6);
x_70 = lean_ctor_get_uint8(x_31, 7);
x_71 = lean_ctor_get_uint8(x_31, 8);
x_72 = lean_ctor_get_uint8(x_31, 10);
x_73 = lean_ctor_get_uint8(x_31, 11);
x_74 = lean_ctor_get_uint8(x_31, 12);
x_75 = lean_ctor_get_uint8(x_31, 13);
x_76 = lean_ctor_get_uint8(x_31, 14);
x_77 = lean_ctor_get_uint8(x_31, 15);
x_78 = lean_ctor_get_uint8(x_31, 16);
x_79 = lean_ctor_get_uint8(x_31, 17);
lean_dec(x_31);
x_80 = 2;
x_81 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_81, 0, x_63);
lean_ctor_set_uint8(x_81, 1, x_64);
lean_ctor_set_uint8(x_81, 2, x_65);
lean_ctor_set_uint8(x_81, 3, x_66);
lean_ctor_set_uint8(x_81, 4, x_67);
lean_ctor_set_uint8(x_81, 5, x_68);
lean_ctor_set_uint8(x_81, 6, x_69);
lean_ctor_set_uint8(x_81, 7, x_70);
lean_ctor_set_uint8(x_81, 8, x_71);
lean_ctor_set_uint8(x_81, 9, x_80);
lean_ctor_set_uint8(x_81, 10, x_72);
lean_ctor_set_uint8(x_81, 11, x_73);
lean_ctor_set_uint8(x_81, 12, x_74);
lean_ctor_set_uint8(x_81, 13, x_75);
lean_ctor_set_uint8(x_81, 14, x_76);
lean_ctor_set_uint8(x_81, 15, x_77);
lean_ctor_set_uint8(x_81, 16, x_78);
lean_ctor_set_uint8(x_81, 17, x_79);
x_82 = 2;
x_83 = lean_uint64_shift_right(x_62, x_82);
x_84 = lean_uint64_shift_left(x_83, x_82);
x_85 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2;
x_86 = lean_uint64_lor(x_84, x_85);
lean_ctor_set(x_7, 0, x_81);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_86);
x_87 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_101 = x_87;
} else {
 lean_dec_ref(x_87);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; uint64_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; lean_object* x_139; lean_object* x_140; 
x_103 = lean_ctor_get(x_7, 0);
x_104 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_105 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_106 = lean_ctor_get(x_7, 1);
x_107 = lean_ctor_get(x_7, 2);
x_108 = lean_ctor_get(x_7, 3);
x_109 = lean_ctor_get(x_7, 4);
x_110 = lean_ctor_get(x_7, 5);
x_111 = lean_ctor_get(x_7, 6);
x_112 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_113 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_103);
lean_dec(x_7);
x_114 = lean_ctor_get_uint8(x_103, 0);
x_115 = lean_ctor_get_uint8(x_103, 1);
x_116 = lean_ctor_get_uint8(x_103, 2);
x_117 = lean_ctor_get_uint8(x_103, 3);
x_118 = lean_ctor_get_uint8(x_103, 4);
x_119 = lean_ctor_get_uint8(x_103, 5);
x_120 = lean_ctor_get_uint8(x_103, 6);
x_121 = lean_ctor_get_uint8(x_103, 7);
x_122 = lean_ctor_get_uint8(x_103, 8);
x_123 = lean_ctor_get_uint8(x_103, 10);
x_124 = lean_ctor_get_uint8(x_103, 11);
x_125 = lean_ctor_get_uint8(x_103, 12);
x_126 = lean_ctor_get_uint8(x_103, 13);
x_127 = lean_ctor_get_uint8(x_103, 14);
x_128 = lean_ctor_get_uint8(x_103, 15);
x_129 = lean_ctor_get_uint8(x_103, 16);
x_130 = lean_ctor_get_uint8(x_103, 17);
if (lean_is_exclusive(x_103)) {
 x_131 = x_103;
} else {
 lean_dec_ref(x_103);
 x_131 = lean_box(0);
}
x_132 = 2;
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 0, 18);
} else {
 x_133 = x_131;
}
lean_ctor_set_uint8(x_133, 0, x_114);
lean_ctor_set_uint8(x_133, 1, x_115);
lean_ctor_set_uint8(x_133, 2, x_116);
lean_ctor_set_uint8(x_133, 3, x_117);
lean_ctor_set_uint8(x_133, 4, x_118);
lean_ctor_set_uint8(x_133, 5, x_119);
lean_ctor_set_uint8(x_133, 6, x_120);
lean_ctor_set_uint8(x_133, 7, x_121);
lean_ctor_set_uint8(x_133, 8, x_122);
lean_ctor_set_uint8(x_133, 9, x_132);
lean_ctor_set_uint8(x_133, 10, x_123);
lean_ctor_set_uint8(x_133, 11, x_124);
lean_ctor_set_uint8(x_133, 12, x_125);
lean_ctor_set_uint8(x_133, 13, x_126);
lean_ctor_set_uint8(x_133, 14, x_127);
lean_ctor_set_uint8(x_133, 15, x_128);
lean_ctor_set_uint8(x_133, 16, x_129);
lean_ctor_set_uint8(x_133, 17, x_130);
x_134 = 2;
x_135 = lean_uint64_shift_right(x_104, x_134);
x_136 = lean_uint64_shift_left(x_135, x_134);
x_137 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2;
x_138 = lean_uint64_lor(x_136, x_137);
x_139 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_106);
lean_ctor_set(x_139, 2, x_107);
lean_ctor_set(x_139, 3, x_108);
lean_ctor_set(x_139, 4, x_109);
lean_ctor_set(x_139, 5, x_110);
lean_ctor_set(x_139, 6, x_111);
lean_ctor_set_uint64(x_139, sizeof(void*)*7, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 8, x_105);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 9, x_112);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 10, x_113);
x_140 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_28, x_4, x_5, x_6, x_139, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
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
x_144 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
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
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_147 = x_140;
} else {
 lean_dec_ref(x_140);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_141, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_149 = x_141;
} else {
 lean_dec_ref(x_141);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 0);
}
lean_ctor_set(x_150, 0, x_148);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_140, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_140, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_154 = x_140;
} else {
 lean_dec_ref(x_140);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_18);
if (x_156 == 0)
{
return x_18;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_18, 0);
x_158 = lean_ctor_get(x_18, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_18);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_15);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_15, 0);
lean_dec(x_161);
x_162 = !lean_is_exclusive(x_16);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_16, 0);
x_164 = lean_box(0);
x_165 = 1;
x_166 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_165);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_166);
return x_15;
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_16, 0);
lean_inc(x_167);
lean_dec(x_16);
x_168 = lean_box(0);
x_169 = 1;
x_170 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*2, x_169);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_15, 0, x_171);
return x_15;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_172 = lean_ctor_get(x_15, 1);
lean_inc(x_172);
lean_dec(x_15);
x_173 = lean_ctor_get(x_16, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_174 = x_16;
} else {
 lean_dec_ref(x_16);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
x_176 = 1;
x_177 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*2, x_176);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_174;
 lean_ctor_set_tag(x_178, 0);
}
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_172);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_15);
if (x_180 == 0)
{
return x_15;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_15, 0);
x_182 = lean_ctor_get(x_15, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_15);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = 0;
lean_inc(x_4);
x_10 = l_Lean_Meta_SplitIf_mkDischarge_x3f(x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Split_getSimpMatchContext(x_4, x_5, x_6, x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed), 11, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
x_17 = l_Lean_Meta_Split_simpMatch___closed__10;
x_18 = l_Lean_Meta_Split_simpMatch___closed__11;
x_19 = l_Lean_Meta_Split_simpMatch___closed__12;
x_20 = 1;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_20);
x_22 = l_Lean_Meta_Split_simpMatch___closed__8;
x_23 = l_Lean_Meta_Simp_main(x_3, x_14, x_22, x_21, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_10, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_19, x_4, x_5, x_6, x_7, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l_Lean_MVarId_replaceTargetEq(x_1, x_23, x_22, x_4, x_5, x_6, x_7, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_3);
x_17 = lean_array_push(x_4, x_8);
x_18 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = lean_infer_type(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isEq(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkHEqRefl(x_7, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_19, x_9, x_10, x_11, x_12, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_26 = l_Lean_Meta_mkEqRefl(x_7, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_27, x_9, x_10, x_11, x_12, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
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
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2;
x_16 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_15, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_1, x_4);
x_21 = lean_array_get(x_19, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_22 = l_Lean_Meta_mkEqHEq(x_20, x_21, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2___boxed), 13, 7);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_6);
lean_closure_set(x_25, 3, x_1);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_3);
lean_closure_set(x_25, 6, x_20);
x_26 = 0;
x_27 = 0;
x_28 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_17, x_26, x_23, x_25, x_27, x_7, x_8, x_9, x_10, x_24);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrGeneralizationFailure", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_isDiscrGenException___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Split_discrGenExId;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Split_isDiscrGenException(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Meta_Split_isDiscrGenException___closed__1;
x_6 = lean_nat_dec_eq(x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_isDiscrGenException___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_isDiscrGenException(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Lean_Meta_mkHEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_array_push(x_3, x_8);
x_20 = lean_array_push(x_4, x_15);
x_21 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_5, x_6, x_7, x_18, x_19, x_20, x_9, x_10, x_11, x_12, x_16);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
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
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Lean_Meta_mkEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_array_push(x_3, x_8);
x_20 = lean_array_push(x_4, x_15);
x_21 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_5, x_6, x_7, x_18, x_19, x_20, x_9, x_10, x_11, x_12, x_16);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
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
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: encountered unexpected auxiliary equalities created to generalize `match`-expression discriminant\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 239, 239);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_7(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_1, x_4);
lean_inc(x_7);
x_17 = l_Lean_Meta_getFVarLocalDecl(x_16, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get(x_15, x_3, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_48; lean_object* x_49; lean_object* x_99; lean_object* x_100; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_48 = l_Lean_LocalDecl_type(x_18);
x_169 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6;
x_170 = lean_unsigned_to_nat(3u);
x_171 = l_Lean_Expr_isAppOfArity(x_22, x_169, x_170);
x_172 = l_Lean_Expr_isAppOfArity(x_48, x_169, x_170);
if (x_171 == 0)
{
lean_object* x_173; 
x_173 = lean_box(0);
x_49 = x_173;
goto block_98;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = l_Lean_Expr_appFn_x21(x_22);
x_175 = l_Lean_Expr_appFn_x21(x_174);
x_176 = l_Lean_Expr_appArg_x21(x_175);
lean_dec(x_175);
x_177 = l_Lean_Expr_appArg_x21(x_174);
lean_dec(x_174);
x_178 = l_Lean_Expr_appArg_x21(x_22);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
if (x_172 == 0)
{
lean_object* x_181; 
x_181 = lean_box(0);
x_99 = x_181;
x_100 = x_180;
goto block_168;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = l_Lean_Expr_appFn_x21(x_48);
x_183 = l_Lean_Expr_appFn_x21(x_182);
x_184 = l_Lean_Expr_appArg_x21(x_183);
lean_dec(x_183);
x_185 = l_Lean_Expr_appArg_x21(x_182);
lean_dec(x_182);
x_186 = l_Lean_Expr_appArg_x21(x_48);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_99 = x_189;
x_100 = x_180;
goto block_168;
}
}
block_47:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_29 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_28, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = l_Lean_Meta_mkHEq(x_33, x_34, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1___boxed), 13, 7);
lean_closure_set(x_39, 0, x_20);
lean_closure_set(x_39, 1, x_4);
lean_closure_set(x_39, 2, x_5);
lean_closure_set(x_39, 3, x_6);
lean_closure_set(x_39, 4, x_1);
lean_closure_set(x_39, 5, x_2);
lean_closure_set(x_39, 6, x_3);
x_40 = 0;
x_41 = 0;
x_42 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_38, x_40, x_36, x_39, x_41, x_7, x_8, x_9, x_10, x_37);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
block_98:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_49);
x_50 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
x_51 = lean_unsigned_to_nat(4u);
x_52 = l_Lean_Expr_isAppOfArity(x_22, x_50, x_51);
x_53 = l_Lean_Expr_isAppOfArity(x_48, x_50, x_51);
if (x_52 == 0)
{
lean_object* x_86; 
lean_dec(x_22);
x_86 = lean_box(0);
x_54 = x_86;
goto block_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = l_Lean_Expr_appFn_x21(x_22);
x_88 = l_Lean_Expr_appFn_x21(x_87);
x_89 = l_Lean_Expr_appFn_x21(x_88);
x_90 = l_Lean_Expr_appArg_x21(x_89);
lean_dec(x_89);
x_91 = l_Lean_Expr_appArg_x21(x_88);
lean_dec(x_88);
x_92 = l_Lean_Expr_appArg_x21(x_87);
lean_dec(x_87);
x_93 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_54 = x_97;
goto block_85;
}
block_85:
{
if (x_53 == 0)
{
lean_dec(x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_56 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_55, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_24 = x_58;
x_25 = x_57;
goto block_47;
}
}
else
{
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_48);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_60 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_59, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = l_Lean_Expr_appFn_x21(x_48);
x_64 = l_Lean_Expr_appFn_x21(x_63);
x_65 = l_Lean_Expr_appFn_x21(x_64);
x_66 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_67 = l_Lean_Expr_appArg_x21(x_64);
lean_dec(x_64);
x_68 = l_Lean_Expr_appArg_x21(x_63);
lean_dec(x_63);
x_69 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_54, 0, x_72);
x_24 = x_54;
x_25 = x_62;
goto block_47;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
lean_dec(x_54);
x_74 = l_Lean_Expr_appFn_x21(x_48);
x_75 = l_Lean_Expr_appFn_x21(x_74);
x_76 = l_Lean_Expr_appFn_x21(x_75);
x_77 = l_Lean_Expr_appArg_x21(x_76);
lean_dec(x_76);
x_78 = l_Lean_Expr_appArg_x21(x_75);
lean_dec(x_75);
x_79 = l_Lean_Expr_appArg_x21(x_74);
lean_dec(x_74);
x_80 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_24 = x_84;
x_25 = x_73;
goto block_47;
}
}
}
}
}
block_168:
{
lean_object* x_101; lean_object* x_102; 
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
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; 
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
x_105 = lean_unsigned_to_nat(4u);
x_106 = l_Lean_Expr_isAppOfArity(x_22, x_104, x_105);
x_107 = l_Lean_Expr_isAppOfArity(x_48, x_104, x_105);
if (x_106 == 0)
{
lean_object* x_140; 
lean_dec(x_22);
x_140 = lean_box(0);
x_108 = x_140;
goto block_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = l_Lean_Expr_appFn_x21(x_22);
x_142 = l_Lean_Expr_appFn_x21(x_141);
x_143 = l_Lean_Expr_appFn_x21(x_142);
x_144 = l_Lean_Expr_appArg_x21(x_143);
lean_dec(x_143);
x_145 = l_Lean_Expr_appArg_x21(x_142);
lean_dec(x_142);
x_146 = l_Lean_Expr_appArg_x21(x_141);
lean_dec(x_141);
x_147 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_144);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_108 = x_151;
goto block_139;
}
block_139:
{
if (x_107 == 0)
{
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_48);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_110 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_109, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_box(0);
x_24 = x_112;
x_25 = x_111;
goto block_47;
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_48);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_114 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_113, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_114;
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = l_Lean_Expr_appFn_x21(x_48);
x_118 = l_Lean_Expr_appFn_x21(x_117);
x_119 = l_Lean_Expr_appFn_x21(x_118);
x_120 = l_Lean_Expr_appArg_x21(x_119);
lean_dec(x_119);
x_121 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_122 = l_Lean_Expr_appArg_x21(x_117);
lean_dec(x_117);
x_123 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
if (lean_is_scalar(x_103)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_103;
}
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_102)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_102;
}
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_108, 0, x_126);
x_24 = x_108;
x_25 = x_116;
goto block_47;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_127 = lean_ctor_get(x_108, 0);
lean_inc(x_127);
lean_dec(x_108);
x_128 = l_Lean_Expr_appFn_x21(x_48);
x_129 = l_Lean_Expr_appFn_x21(x_128);
x_130 = l_Lean_Expr_appFn_x21(x_129);
x_131 = l_Lean_Expr_appArg_x21(x_130);
lean_dec(x_130);
x_132 = l_Lean_Expr_appArg_x21(x_129);
lean_dec(x_129);
x_133 = l_Lean_Expr_appArg_x21(x_128);
lean_dec(x_128);
x_134 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
if (lean_is_scalar(x_103)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_103;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_102)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_102;
}
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_24 = x_138;
x_25 = x_127;
goto block_47;
}
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_102);
lean_dec(x_48);
lean_dec(x_22);
x_152 = lean_ctor_get(x_99, 0);
lean_inc(x_152);
lean_dec(x_99);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_101, 1);
lean_inc(x_154);
lean_dec(x_101);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = l_Lean_Meta_mkEq(x_154, x_155, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_160 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2___boxed), 13, 7);
lean_closure_set(x_160, 0, x_20);
lean_closure_set(x_160, 1, x_4);
lean_closure_set(x_160, 2, x_5);
lean_closure_set(x_160, 3, x_6);
lean_closure_set(x_160, 4, x_1);
lean_closure_set(x_160, 5, x_2);
lean_closure_set(x_160, 6, x_3);
x_161 = 0;
x_162 = 0;
x_163 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_159, x_161, x_157, x_160, x_162, x_7, x_8, x_9, x_10, x_158);
return x_163;
}
else
{
uint8_t x_164; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_156);
if (x_164 == 0)
{
return x_156;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_156, 0);
x_166 = lean_ctor_get(x_156, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_156);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_21);
if (x_190 == 0)
{
return x_21;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_21, 0);
x_192 = lean_ctor_get(x_21, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_21);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_17);
if (x_194 == 0)
{
return x_17;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_17, 0);
x_196 = lean_ctor_get(x_17, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_17);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_array_push(x_4, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 4);
x_11 = l_Array_zip___rarg(x_2, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1(x_11, x_13, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_3, x_4, x_14, x_13, x_15, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Match.MatcherApp.Basic", 32, 32);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.matchMatcherApp\?", 26, 26);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1;
x_2 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(63u);
x_4 = lean_unsigned_to_nat(53u);
x_5 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_20 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 1:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_5);
x_15 = x_21;
x_16 = x_27;
goto block_19;
}
else
{
uint8_t x_28; 
lean_free_object(x_21);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_33, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_15 = x_36;
x_16 = x_35;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
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
case 6:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_43, 4);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_push(x_5, x_44);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_45);
x_15 = x_21;
x_16 = x_41;
goto block_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_46, 4);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_array_push(x_5, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_15 = x_49;
x_16 = x_41;
goto block_19;
}
}
default: 
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_21, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_dec(x_20);
x_53 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_53, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_5);
x_15 = x_21;
x_16 = x_55;
goto block_19;
}
else
{
uint8_t x_56; 
lean_free_object(x_21);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_21);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_dec(x_20);
x_61 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_61, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_5);
x_15 = x_64;
x_16 = x_63;
goto block_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_20);
if (x_69 == 0)
{
return x_20;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_20, 0);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_20);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_19:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_14;
x_5 = x_17;
x_6 = lean_box(0);
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_20 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 1:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_5);
x_15 = x_21;
x_16 = x_27;
goto block_19;
}
else
{
uint8_t x_28; 
lean_free_object(x_21);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_33, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_15 = x_36;
x_16 = x_35;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
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
case 6:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_43, 4);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_push(x_5, x_44);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_45);
x_15 = x_21;
x_16 = x_41;
goto block_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_46, 4);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_array_push(x_5, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_15 = x_49;
x_16 = x_41;
goto block_19;
}
}
default: 
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_21, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_dec(x_20);
x_53 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_53, x_7, x_8, x_9, x_10, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_5);
x_15 = x_21;
x_16 = x_55;
goto block_19;
}
else
{
uint8_t x_56; 
lean_free_object(x_21);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_21);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_dec(x_20);
x_61 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2(x_61, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_5);
x_15 = x_64;
x_16 = x_63;
goto block_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_20);
if (x_69 == 0)
{
return x_20;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_20, 0);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_20);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_19:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_14;
x_5 = x_17;
x_6 = lean_box(0);
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_2);
x_13 = l_Array_toSubarray___rarg(x_2, x_12, x_11);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_array_get(x_14, x_2, x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_11, x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_nat_add(x_19, x_16);
lean_dec(x_19);
lean_inc(x_20);
lean_inc(x_2);
x_21 = l_Array_toSubarray___rarg(x_2, x_17, x_20);
x_22 = lean_nat_add(x_18, x_16);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_mk_array(x_22, x_23);
x_25 = l_Lean_InductiveVal_numCtors(x_1);
x_26 = lean_nat_add(x_20, x_25);
lean_dec(x_25);
lean_inc(x_26);
lean_inc(x_2);
x_27 = l_Array_toSubarray___rarg(x_2, x_20, x_26);
x_28 = lean_array_get_size(x_2);
x_29 = l_Array_toSubarray___rarg(x_2, x_26, x_28);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_List_lengthTRAux___rarg(x_31, x_12);
lean_dec(x_31);
x_33 = l_List_lengthTRAux___rarg(x_3, x_12);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
x_35 = lean_box(0);
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 4);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
lean_inc(x_36);
x_38 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3(x_35, x_36, x_36, x_36, x_37, lean_box(0), x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_array_mk(x_3);
x_42 = l_Array_ofSubarray___rarg(x_13);
lean_dec(x_13);
x_43 = l_Array_ofSubarray___rarg(x_21);
lean_dec(x_21);
x_44 = l_Array_ofSubarray___rarg(x_27);
lean_dec(x_27);
x_45 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_46 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1;
x_47 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_24);
lean_ctor_set(x_47, 4, x_42);
lean_ctor_set(x_47, 5, x_15);
lean_ctor_set(x_47, 6, x_43);
lean_ctor_set(x_47, 7, x_40);
lean_ctor_set(x_47, 8, x_44);
lean_ctor_set(x_47, 9, x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_38, 0, x_48);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_array_mk(x_3);
x_52 = l_Array_ofSubarray___rarg(x_13);
lean_dec(x_13);
x_53 = l_Array_ofSubarray___rarg(x_21);
lean_dec(x_21);
x_54 = l_Array_ofSubarray___rarg(x_27);
lean_dec(x_27);
x_55 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_56 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1;
x_57 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_24);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_15);
lean_ctor_set(x_57, 6, x_53);
lean_ctor_set(x_57, 7, x_49);
lean_ctor_set(x_57, 8, x_54);
lean_ctor_set(x_57, 9, x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_50);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_38);
if (x_60 == 0)
{
return x_38;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
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
x_64 = lean_ctor_get(x_1, 4);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
lean_inc(x_64);
x_66 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4(x_35, x_64, x_64, x_64, x_65, lean_box(0), x_6, x_7, x_8, x_9, x_10);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_array_mk(x_3);
x_70 = l_Array_ofSubarray___rarg(x_13);
lean_dec(x_13);
x_71 = l_Array_ofSubarray___rarg(x_21);
lean_dec(x_21);
x_72 = l_Array_ofSubarray___rarg(x_27);
lean_dec(x_27);
x_73 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_74 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_23);
lean_ctor_set(x_74, 3, x_24);
lean_ctor_set(x_74, 4, x_70);
lean_ctor_set(x_74, 5, x_15);
lean_ctor_set(x_74, 6, x_71);
lean_ctor_set(x_74, 7, x_68);
lean_ctor_set(x_74, 8, x_72);
lean_ctor_set(x_74, 9, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_66, 0, x_75);
return x_66;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_66, 0);
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_66);
x_78 = lean_array_mk(x_3);
x_79 = l_Array_ofSubarray___rarg(x_13);
lean_dec(x_13);
x_80 = l_Array_ofSubarray___rarg(x_21);
lean_dec(x_21);
x_81 = l_Array_ofSubarray___rarg(x_27);
lean_dec(x_27);
x_82 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_83 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_23);
lean_ctor_set(x_83, 3, x_24);
lean_ctor_set(x_83, 4, x_79);
lean_ctor_set(x_83, 5, x_15);
lean_ctor_set(x_83, 6, x_80);
lean_ctor_set(x_83, 7, x_76);
lean_ctor_set(x_83, 8, x_81);
lean_ctor_set(x_83, 9, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_66);
if (x_86 == 0)
{
return x_66;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_66, 0);
x_88 = lean_ctor_get(x_66, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_66);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_st_ref_get(x_10, x_11);
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_2, x_14, x_7, x_8, x_9, x_10, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_casesOnSuffix;
lean_inc(x_3);
x_20 = l_Lean_isAuxRecursorWithSuffix(x_18, x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_apply_6(x_2, x_21, x_7, x_8, x_9, x_10, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Name_getPrefix(x_3);
x_24 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_23, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 5)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_30);
x_32 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_33, x_35);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
x_38 = lean_nat_add(x_37, x_34);
lean_dec(x_37);
x_39 = lean_ctor_get(x_29, 2);
lean_inc(x_39);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_41 = lean_nat_add(x_40, x_34);
lean_dec(x_40);
x_42 = l_Lean_InductiveVal_numCtors(x_29);
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_36);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_46 = lean_box(0);
lean_ctor_set(x_24, 0, x_46);
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_24);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2(x_29, x_36, x_5, x_3, x_47, x_7, x_8, x_9, x_10, x_27);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
lean_dec(x_25);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_51);
x_53 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_54, x_56);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
x_59 = lean_nat_add(x_58, x_55);
lean_dec(x_58);
x_60 = lean_ctor_get(x_50, 2);
lean_inc(x_60);
x_61 = lean_nat_add(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_62 = lean_nat_add(x_61, x_55);
lean_dec(x_61);
x_63 = l_Lean_InductiveVal_numCtors(x_50);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_57);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_49);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2(x_50, x_57, x_5, x_3, x_69, x_7, x_8, x_9, x_10, x_49);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_24, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_24, 0, x_73);
return x_24;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_24, 1);
lean_inc(x_74);
lean_dec(x_24);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_24);
if (x_77 == 0)
{
return x_24;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_24, 0);
x_79 = lean_ctor_get(x_24, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_24);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_11 = lean_array_mk(x_1);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_extract___rarg(x_3, x_15, x_14);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_3, x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_nat_add(x_20, x_21);
lean_inc(x_22);
lean_inc(x_3);
x_23 = l_Array_toSubarray___rarg(x_3, x_20, x_22);
x_24 = l_Array_ofSubarray___rarg(x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_2);
x_27 = lean_nat_add(x_22, x_26);
lean_dec(x_26);
lean_inc(x_27);
lean_inc(x_3);
x_28 = l_Array_toSubarray___rarg(x_3, x_22, x_27);
x_29 = l_Array_ofSubarray___rarg(x_28);
lean_dec(x_28);
x_30 = lean_array_get_size(x_3);
x_31 = l_Array_toSubarray___rarg(x_3, x_27, x_30);
x_32 = l_Array_ofSubarray___rarg(x_31);
lean_dec(x_31);
lean_inc(x_25);
lean_inc(x_13);
lean_inc(x_12);
x_33 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_12);
lean_ctor_set(x_33, 3, x_13);
lean_ctor_set(x_33, 4, x_16);
lean_ctor_set(x_33, 5, x_18);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_29);
lean_ctor_set(x_33, 9, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1;
x_9 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3(x_2, x_8, x_10, x_1, x_11, x_15, x_3, x_4, x_5, x_6, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_21);
x_23 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_24, x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Meta_Match_MatcherInfo_arity(x_20);
x_30 = lean_nat_dec_lt(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_12);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4(x_11, x_20, x_27, x_10, x_31, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_36);
x_38 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_39, x_41);
x_43 = lean_array_get_size(x_42);
x_44 = l_Lean_Meta_Match_MatcherInfo_arity(x_35);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4(x_11, x_35, x_42, x_10, x_46, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_35);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_apply_6(x_8, x_50, x_3, x_4, x_5, x_6, x_7);
return x_51;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discr mismatch ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" != ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_25; 
x_15 = lean_array_uget(x_4, x_6);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_15);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_7);
x_16 = x_32;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_26, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_28, x_29);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_29, x_38);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_39);
x_40 = lean_expr_eqv(x_15, x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_free_object(x_7);
x_41 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_42 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_41, x_8, x_9, x_10, x_11, x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_15);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_26, x_46, x_8, x_9, x_10, x_11, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_16 = x_48;
x_17 = x_49;
goto block_24;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_51 = lean_ctor_get(x_42, 1);
x_52 = lean_ctor_get(x_42, 0);
lean_dec(x_52);
x_53 = l_Lean_MessageData_ofExpr(x_15);
x_54 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_54);
x_55 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_37);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_41, x_60, x_8, x_9, x_10, x_11, x_51);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_26, x_62, x_8, x_9, x_10, x_11, x_63);
lean_dec(x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_16 = x_65;
x_17 = x_66;
goto block_24;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_dec(x_42);
x_68 = l_Lean_MessageData_ofExpr(x_15);
x_69 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_MessageData_ofExpr(x_37);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_41, x_76, x_8, x_9, x_10, x_11, x_67);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_26, x_78, x_8, x_9, x_10, x_11, x_79);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_16 = x_81;
x_17 = x_82;
goto block_24;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_37);
lean_dec(x_15);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_7);
x_16 = x_83;
x_17 = x_12;
goto block_24;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_26);
x_84 = lean_array_fget(x_28, x_29);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_29, x_85);
lean_dec(x_29);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_28);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_30);
x_88 = lean_expr_eqv(x_15, x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_free_object(x_7);
x_89 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_90 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_89, x_8, x_9, x_10, x_11, x_12);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_84);
lean_dec(x_15);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_95 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_87, x_94, x_8, x_9, x_10, x_11, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_16 = x_96;
x_17 = x_97;
goto block_24;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
x_100 = l_Lean_MessageData_ofExpr(x_15);
x_101 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5;
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_99;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_MessageData_ofExpr(x_84);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_89, x_108, x_8, x_9, x_10, x_11, x_98);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_87, x_110, x_8, x_9, x_10, x_11, x_111);
lean_dec(x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_16 = x_113;
x_17 = x_114;
goto block_24;
}
}
else
{
lean_object* x_115; 
lean_dec(x_84);
lean_dec(x_15);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_87);
lean_ctor_set(x_7, 0, x_3);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_7);
x_16 = x_115;
x_17 = x_12;
goto block_24;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_7, 1);
lean_inc(x_116);
lean_dec(x_7);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 2);
lean_inc(x_119);
x_120 = lean_nat_dec_lt(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_15);
lean_inc(x_3);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_3);
lean_ctor_set(x_121, 1, x_116);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_16 = x_122;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
x_124 = lean_array_fget(x_117, x_118);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_118, x_125);
lean_dec(x_118);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 3, 0);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_119);
x_128 = lean_expr_eqv(x_15, x_124);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_130 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_129, x_8, x_9, x_10, x_11, x_12);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_124);
lean_dec(x_15);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_box(0);
x_135 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_127, x_134, x_8, x_9, x_10, x_11, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_16 = x_136;
x_17 = x_137;
goto block_24;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_139 = x_130;
} else {
 lean_dec_ref(x_130);
 x_139 = lean_box(0);
}
x_140 = l_Lean_MessageData_ofExpr(x_15);
x_141 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5;
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(7, 2, 0);
} else {
 x_142 = x_139;
 lean_ctor_set_tag(x_142, 7);
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_MessageData_ofExpr(x_124);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_129, x_148, x_8, x_9, x_10, x_11, x_138);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_127, x_150, x_8, x_9, x_10, x_11, x_151);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_16 = x_153;
x_17 = x_154;
goto block_24;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_124);
lean_dec(x_15);
lean_inc(x_3);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_3);
lean_ctor_set(x_155, 1, x_127);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_16 = x_156;
x_17 = x_12;
goto block_24;
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_11 = l_Lean_Expr_replaceFVars(x_1, x_2, x_5);
x_12 = l_Array_ofSubarray___rarg(x_3);
x_13 = l_Array_append___rarg(x_12, x_4);
x_14 = 0;
x_15 = 1;
x_16 = 1;
x_17 = l_Lean_Meta_mkLambdaFVars(x_13, x_11, x_14, x_15, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_9);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Array_toSubarray___rarg(x_9, x_10, x_20);
x_22 = l_Array_ofSubarray___rarg(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_22, x_18, x_23, x_24, x_23, x_25, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_sub(x_10, x_4);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_29);
lean_inc(x_9);
x_31 = l_Array_toSubarray___rarg(x_9, x_30, x_29);
x_32 = lean_nat_dec_eq(x_4, x_30);
lean_dec(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Array_toSubarray___rarg(x_9, x_29, x_10);
x_34 = l_Array_ofSubarray___rarg(x_33);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1___boxed), 10, 3);
lean_closure_set(x_35, 0, x_27);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_31);
x_36 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_3, x_6, x_34, x_35, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_6);
lean_dec(x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_37 = l_Array_ofSubarray___rarg(x_31);
lean_dec(x_31);
x_38 = l_Lean_Meta_mkLambdaFVars(x_37, x_27, x_23, x_24, x_23, x_25, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: encountered an unexpected `match` expression alternative\nthis error typically occurs when the `match` expression has been constructed using meta-programming.", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_9);
x_17 = lean_nat_dec_lt(x_16, x_8);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_16, x_4);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9, x_8, x_19, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2;
x_22 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_21, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2;
x_28 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_27, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_nat_dec_lt(x_13, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_array_fget(x_9, x_13);
x_25 = l_instInhabitedNat;
x_26 = lean_array_get(x_25, x_8, x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3), 15, 8);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_5);
lean_closure_set(x_27, 5, x_6);
lean_closure_set(x_27, 6, x_7);
lean_closure_set(x_27, 7, x_26);
x_28 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_29 = l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(x_24, x_27, x_28, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_push(x_12, x_30);
x_33 = lean_ctor_get(x_11, 2);
x_34 = lean_nat_add(x_13, x_33);
lean_dec(x_13);
x_12 = x_32;
x_13 = x_34;
x_14 = lean_box(0);
x_15 = lean_box(0);
x_20 = x_31;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_4);
lean_ctor_set(x_23, 4, x_5);
lean_ctor_set(x_23, 5, x_6);
lean_ctor_set(x_23, 6, x_7);
lean_ctor_set(x_23, 7, x_8);
lean_ctor_set(x_23, 8, x_9);
lean_ctor_set(x_23, 9, x_10);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_st_ref_set(x_11, x_25, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_9);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
lean_inc(x_7);
x_33 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6(x_12, x_13, x_14, x_15, x_7, x_16, x_11, x_8, x_9, x_23, x_31, x_32, x_29, lean_box(0), lean_box(0), x_18, x_19, x_20, x_21, x_27);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_9);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_3);
lean_ctor_set(x_36, 3, x_4);
lean_ctor_set(x_36, 4, x_5);
lean_ctor_set(x_36, 5, x_6);
lean_ctor_set(x_36, 6, x_7);
lean_ctor_set(x_36, 7, x_8);
lean_ctor_set(x_36, 8, x_35);
lean_ctor_set(x_36, 9, x_10);
x_37 = l_Lean_Meta_MatcherApp_toExpr(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_4);
lean_ctor_set(x_41, 4, x_5);
lean_ctor_set(x_41, 5, x_6);
lean_ctor_set(x_41, 6, x_7);
lean_ctor_set(x_41, 7, x_8);
lean_ctor_set(x_41, 8, x_39);
lean_ctor_set(x_41, 9, x_10);
x_42 = l_Lean_Meta_MatcherApp_toExpr(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_15, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_array_get_size(x_2);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_28 = l_Array_toSubarray___rarg(x_2, x_27, x_26);
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_25, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_25, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_25, 8);
lean_inc(x_38);
x_39 = lean_ctor_get(x_25, 9);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
x_42 = lean_array_size(x_36);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5(x_29, x_36, x_40, x_36, x_42, x_43, x_41, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_36);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1(x_30, x_31, x_32, x_33, x_34, x_35, x_3, x_37, x_38, x_39, x_4, x_5, x_2, x_6, x_7, x_8, x_48, x_10, x_11, x_12, x_13, x_47);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_44, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_16);
if (x_56 == 0)
{
return x_16;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Meta_Match_MatcherInfo_arity(x_5);
x_15 = l_Lean_Expr_isAppOfArity(x_8, x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Meta_Split_simpMatch___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__3), 13, 7);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_3);
lean_closure_set(x_14, 5, x_4);
lean_closure_set(x_14, 6, x_6);
x_15 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1;
x_19 = 0;
x_20 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_16, x_14, x_18, x_19, x_19, x_9, x_10, x_11, x_12, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___boxed(lean_object** _args) {
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
x_21 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1___boxed(lean_object** _args) {
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
x_23 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_17);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_fvarId_x21(x_5);
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
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Split_isDiscrGenException___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = l_Array_append___rarg(x_1, x_2);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_11, x_3, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_18 = l_Lean_Meta_isTypeCorrect(x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1(x_16, x_4, x_28, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: failed to find match-expression discriminants\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 187, 187);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_st_mk_ref(x_15, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MVarId_getType(x_1, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_20, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_17, x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2;
x_30 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_29, x_9, x_10, x_11, x_12, x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2(x_6, x_7, x_23, x_8, x_36, x_9, x_10, x_11, x_12, x_35);
lean_dec(x_7);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3), 13, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_6);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___rarg(x_3, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_inc(x_1);
x_11 = l_Lean_mkAppN(x_1, x_2);
x_12 = l_Lean_mkAppN(x_11, x_3);
x_13 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_4, x_12, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
x_16 = lean_array_get_size(x_2);
x_17 = lean_box(0);
x_18 = 0;
x_19 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_20 = l_Lean_Meta_introNCore(x_15, x_16, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = l_Lean_Meta_introNCore(x_25, x_16, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_21, 1, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_21);
lean_dec(x_24);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = l_Lean_Meta_introNCore(x_45, x_16, x_17, x_18, x_19, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_58 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
uint8_t x_60; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Split", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Split.0.Lean.Meta.Split.generalizeMatchDiscrs", 71, 71);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2;
x_3 = lean_unsigned_to_nat(125u);
x_4 = lean_unsigned_to_nat(59u);
x_5 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("targetNew:\n", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3;
x_15 = l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(x_14, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4___boxed), 12, 5);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_19);
x_21 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_4, x_20, x_21, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_2);
x_27 = l_Lean_MVarId_getTag(x_2, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_6);
x_30 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_25, x_28, x_6, x_7, x_8, x_9, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_35 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_34, x_6, x_7, x_8, x_9, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_30);
lean_free_object(x_12);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_32, x_3, x_26, x_2, x_39, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_26);
lean_dec(x_3);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_35, 1);
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_44);
x_45 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5;
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_35, 0, x_45);
x_46 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_46);
lean_ctor_set(x_30, 0, x_35);
x_47 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_34, x_30, x_6, x_7, x_8, x_9, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_32, x_3, x_26, x_2, x_48, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_52);
x_53 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_12);
x_55 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_55);
lean_ctor_set(x_30, 0, x_54);
x_56 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_34, x_30, x_6, x_7, x_8, x_9, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_32, x_3, x_26, x_2, x_57, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_57);
lean_dec(x_26);
lean_dec(x_3);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_30, 0);
x_61 = lean_ctor_get(x_30, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_30);
x_62 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_63 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_62, x_6, x_7, x_8, x_9, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_12);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_box(0);
x_68 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_60, x_3, x_26, x_2, x_67, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_26);
lean_dec(x_3);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Expr_mvarId_x21(x_60);
lean_ctor_set(x_12, 0, x_71);
x_72 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5;
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_70;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_12);
x_74 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_62, x_75, x_6, x_7, x_8, x_9, x_69);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_60, x_3, x_26, x_2, x_77, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_77);
lean_dec(x_26);
lean_dec(x_3);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_27);
if (x_80 == 0)
{
return x_27;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_27, 0);
x_82 = lean_ctor_get(x_27, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_27);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_22);
if (x_84 == 0)
{
return x_22;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_22, 0);
x_86 = lean_ctor_get(x_22, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_22);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_12, 0);
lean_inc(x_88);
lean_dec(x_12);
x_89 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_88);
lean_inc(x_3);
lean_inc(x_2);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4___boxed), 12, 5);
lean_closure_set(x_90, 0, x_2);
lean_closure_set(x_90, 1, x_1);
lean_closure_set(x_90, 2, x_3);
lean_closure_set(x_90, 3, x_88);
lean_closure_set(x_90, 4, x_89);
x_91 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_92 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_4, x_90, x_91, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_2);
x_97 = l_Lean_MVarId_getTag(x_2, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_6);
x_100 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_95, x_98, x_6, x_7, x_8, x_9, x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_105 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_104, x_6, x_7, x_8, x_9, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_103);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_box(0);
x_110 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_101, x_3, x_96, x_2, x_109, x_6, x_7, x_8, x_9, x_108);
lean_dec(x_96);
lean_dec(x_3);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
x_113 = l_Lean_Expr_mvarId_x21(x_101);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5;
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_112;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
if (lean_is_scalar(x_103)) {
 x_118 = lean_alloc_ctor(7, 2, 0);
} else {
 x_118 = x_103;
 lean_ctor_set_tag(x_118, 7);
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_104, x_118, x_6, x_7, x_8, x_9, x_111);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_101, x_3, x_96, x_2, x_120, x_6, x_7, x_8, x_9, x_121);
lean_dec(x_120);
lean_dec(x_96);
lean_dec(x_3);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_97, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_97, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_125 = x_97;
} else {
 lean_dec_ref(x_97);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_92, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_92, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_129 = x_92;
} else {
 lean_dec_ref(x_92);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_get_size(x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_10 = x_23;
goto block_19;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_26 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(x_4, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_10 = x_27;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_box(0);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___boxed), 10, 5);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_4);
lean_closure_set(x_29, 3, x_3);
lean_closure_set(x_29, 4, x_28);
x_30 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_29, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
}
block_19:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_11 = lean_array_size(x_4);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(x_11, x_12, x_4);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Lean_Expr_fvar___override(x_14);
lean_inc(x_22);
x_25 = l_Lean_Meta_FVarSubst_apply(x_22, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_heqToEq(x_23, x_26, x_27, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_32);
lean_inc(x_33);
x_35 = l_Lean_Meta_substCore_x3f(x_33, x_32, x_34, x_22, x_27, x_34, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_33);
x_38 = l_Lean_Meta_substCore_x3f(x_33, x_32, x_27, x_22, x_27, x_34, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_ctor_set(x_29, 0, x_22);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_29);
x_15 = x_41;
x_16 = x_40;
goto block_21;
}
else
{
uint8_t x_42; 
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_22);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
x_15 = x_39;
x_16 = x_44;
goto block_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_39, 0, x_48);
x_15 = x_39;
x_16 = x_44;
goto block_21;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_15 = x_55;
x_16 = x_50;
goto block_21;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
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
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_22);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_36, 0);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
x_15 = x_36;
x_16 = x_62;
goto block_21;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_36, 0, x_66);
x_15 = x_36;
x_16 = x_62;
goto block_21;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_36, 0);
lean_inc(x_67);
lean_dec(x_36);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_dec(x_35);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_15 = x_73;
x_16 = x_68;
goto block_21;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_29);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
return x_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_35, 0);
x_76 = lean_ctor_get(x_35, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_35);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_29, 0);
x_79 = lean_ctor_get(x_29, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_29);
x_80 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_78);
lean_inc(x_79);
x_81 = l_Lean_Meta_substCore_x3f(x_79, x_78, x_80, x_22, x_27, x_80, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_79);
x_84 = l_Lean_Meta_substCore_x3f(x_79, x_78, x_27, x_22, x_27, x_80, x_7, x_8, x_9, x_10, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_22);
lean_ctor_set(x_87, 1, x_79);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_15 = x_88;
x_16 = x_86;
goto block_21;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_79);
lean_dec(x_22);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_95);
x_15 = x_96;
x_16 = x_91;
goto block_21;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_79);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = lean_ctor_get(x_84, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_99 = x_84;
} else {
 lean_dec_ref(x_84);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_22);
x_101 = lean_ctor_get(x_82, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_102 = x_82;
} else {
 lean_dec_ref(x_82);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
lean_dec(x_81);
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_106 = x_101;
} else {
 lean_dec_ref(x_101);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
x_15 = x_108;
x_16 = x_103;
goto block_21;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_109 = lean_ctor_get(x_81, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_81, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_111 = x_81;
} else {
 lean_dec_ref(x_81);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_113 = !lean_is_exclusive(x_28);
if (x_113 == 0)
{
return x_28;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_28, 0);
x_115 = lean_ctor_get(x_28, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_28);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_25);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_22);
lean_ctor_set(x_117, 1, x_23);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_15 = x_118;
x_16 = x_11;
goto block_21;
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(x_1, x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_array_size(x_3);
x_12 = lean_box_usize(x_11);
x_13 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1;
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1___boxed), 10, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_10);
x_15 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lambda__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after unifyEqs\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_1);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Meta_Cases_unifyEqs_x3f(x_15, x_3, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_6);
x_36 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_9, x_10, x_11, x_12, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_31);
lean_free_object(x_19);
lean_dec(x_6);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_34, x_35, x_7, x_4, x_5, x_40, x_9, x_10, x_11, x_12, x_39);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_36, 1);
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
lean_inc(x_34);
lean_ctor_set(x_19, 0, x_34);
x_45 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_19);
lean_ctor_set(x_36, 0, x_45);
x_46 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_46);
lean_ctor_set(x_31, 0, x_36);
x_47 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_6, x_31, x_9, x_10, x_11, x_12, x_43);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_34, x_35, x_7, x_4, x_5, x_48, x_9, x_10, x_11, x_12, x_49);
lean_dec(x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_34);
lean_ctor_set(x_19, 0, x_34);
x_52 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_19);
x_54 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_54);
lean_ctor_set(x_31, 0, x_53);
x_55 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_6, x_31, x_9, x_10, x_11, x_12, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_34, x_35, x_7, x_4, x_5, x_56, x_9, x_10, x_11, x_12, x_57);
lean_dec(x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
lean_inc(x_6);
x_61 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_9, x_10, x_11, x_12, x_32);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_19);
lean_dec(x_6);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_59, x_60, x_7, x_4, x_5, x_65, x_9, x_10, x_11, x_12, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
lean_inc(x_59);
lean_ctor_set(x_19, 0, x_59);
x_69 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2;
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(7, 2, 0);
} else {
 x_70 = x_68;
 lean_ctor_set_tag(x_70, 7);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_19);
x_71 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_6, x_72, x_9, x_10, x_11, x_12, x_67);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_59, x_60, x_7, x_4, x_5, x_74, x_9, x_10, x_11, x_12, x_75);
lean_dec(x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = lean_ctor_get(x_19, 0);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_dec(x_18);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
lean_inc(x_6);
x_82 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_9, x_10, x_11, x_12, x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
lean_dec(x_6);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_box(0);
x_87 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_79, x_80, x_7, x_4, x_5, x_86, x_9, x_10, x_11, x_12, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_89 = x_82;
} else {
 lean_dec_ref(x_82);
 x_89 = lean_box(0);
}
lean_inc(x_79);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_79);
x_91 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2;
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(7, 2, 0);
} else {
 x_92 = x_89;
 lean_ctor_set_tag(x_92, 7);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_81;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_6, x_94, x_9, x_10, x_11, x_12, x_88);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_79, x_80, x_7, x_4, x_5, x_96, x_9, x_10, x_11, x_12, x_97);
lean_dec(x_96);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("before unifyEqs\n", 16, 16);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_2, 2);
x_20 = l_instInhabitedNat;
x_21 = lean_array_get(x_20, x_19, x_17);
x_22 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_23 = l_Lean_Meta_introNCore(x_15, x_21, x_6, x_22, x_22, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
lean_inc(x_3);
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_9, x_10, x_11, x_12, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_24);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_5, x_27, x_17, x_18, x_3, x_4, x_33, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_7 = x_35;
x_8 = x_16;
x_13 = x_36;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_29, 1);
x_44 = lean_ctor_get(x_29, 0);
lean_dec(x_44);
lean_inc(x_27);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_27);
x_46 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_45);
lean_ctor_set(x_29, 0, x_46);
x_47 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_47);
lean_ctor_set(x_24, 0, x_29);
lean_inc(x_3);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_24, x_9, x_10, x_11, x_12, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_5, x_27, x_17, x_18, x_3, x_4, x_49, x_9, x_10, x_11, x_12, x_50);
lean_dec(x_49);
lean_dec(x_17);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_7 = x_52;
x_8 = x_16;
x_13 = x_53;
goto _start;
}
else
{
uint8_t x_55; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_29, 1);
lean_inc(x_59);
lean_dec(x_29);
lean_inc(x_27);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_27);
x_61 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_63);
lean_ctor_set(x_24, 0, x_62);
lean_inc(x_3);
x_64 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_24, x_9, x_10, x_11, x_12, x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_67 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_5, x_27, x_17, x_18, x_3, x_4, x_65, x_9, x_10, x_11, x_12, x_66);
lean_dec(x_65);
lean_dec(x_17);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_7 = x_68;
x_8 = x_16;
x_13 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
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
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_24, 1);
lean_inc(x_75);
lean_dec(x_24);
lean_inc(x_3);
x_76 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_9, x_10, x_11, x_12, x_25);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_5, x_75, x_17, x_18, x_3, x_4, x_80, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_17);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_7 = x_82;
x_8 = x_16;
x_13 = x_83;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_90 = x_76;
} else {
 lean_dec_ref(x_76);
 x_90 = lean_box(0);
}
lean_inc(x_75);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_75);
x_92 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(7, 2, 0);
} else {
 x_93 = x_90;
 lean_ctor_set_tag(x_93, 7);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_3);
x_96 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_95, x_9, x_10, x_11, x_12, x_89);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_5, x_75, x_17, x_18, x_3, x_4, x_97, x_9, x_10, x_11, x_12, x_98);
lean_dec(x_97);
lean_dec(x_17);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_7 = x_100;
x_8 = x_16;
x_13 = x_101;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_23);
if (x_107 == 0)
{
return x_23;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_23, 0);
x_109 = lean_ctor_get(x_23, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_23);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrEqs after generalizeTargetsEq: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_array_size(x_2);
x_20 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_19, x_3, x_2);
x_21 = lean_array_to_list(x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_21, x_22);
x_24 = l_Lean_MessageData_ofList(x_23);
x_25 = l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_28, x_4, x_5, x_6, x_7, x_18);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(x_2, x_3, x_4, x_5, x_6, x_1, x_15, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_List_reverse___rarg(x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_List_reverse___rarg(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1() {
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
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: unexpected number of goals created after applying splitter auxiliary theorem `", 112, 112);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` for `", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = l_Lean_MVarId_apply(x_1, x_2, x_17, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_List_lengthTRAux___rarg(x_19, x_21);
x_23 = l_Lean_Meta_Match_MatchEqns_size(x_5);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_25 = l_Lean_MessageData_ofName(x_9);
x_26 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofName(x_10);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_33, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2(x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_39, x_12, x_13, x_14, x_15, x_20);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after check splitter", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_18, x_19, x_18, x_20, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_app___override(x_3, x_22);
x_25 = l_Lean_mkAppN(x_24, x_1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_25);
x_26 = l_Lean_Meta_check(x_25, x_13, x_14, x_15, x_16, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_4);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_13, x_14, x_15, x_16, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_5, x_25, x_6, x_7, x_8, x_4, x_9, x_10, x_11, x_12, x_32, x_13, x_14, x_15, x_16, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2;
lean_inc(x_4);
x_36 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_35, x_13, x_14, x_15, x_16, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_5, x_25, x_6, x_7, x_8, x_4, x_9, x_10, x_11, x_12, x_37, x_13, x_14, x_15, x_16, x_38);
lean_dec(x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_to_list(x_13);
lean_inc(x_1);
x_20 = l_Lean_Expr_const___override(x_1, x_19);
x_21 = l_Lean_mkAppN(x_20, x_2);
lean_inc(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lambda__4___boxed), 17, 12);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_8);
lean_closure_set(x_22, 7, x_9);
lean_closure_set(x_22, 8, x_10);
lean_closure_set(x_22, 9, x_11);
lean_closure_set(x_22, 10, x_1);
lean_closure_set(x_22, 11, x_12);
x_23 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_6, x_22, x_14, x_15, x_16, x_17, x_18);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed to split a match-expression: the splitter auxiliary theorem `", 83, 83);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` can only eliminate into `Prop`", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
size_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_array_size(x_1);
x_21 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_20, x_2, x_1);
lean_inc(x_3);
x_22 = l_Lean_MVarId_getType(x_3, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel), 6, 1);
lean_closure_set(x_25, 0, x_23);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
x_26 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_3, x_25, x_15, x_16, x_17, x_18, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_8, 3);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Level_isZero(x_28);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_31 = l_Lean_MessageData_ofName(x_4);
x_32 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_35, x_15, x_16, x_17, x_18, x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5(x_4, x_5, x_21, x_23, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_15, x_16, x_17, x_18, x_29);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_array_set(x_13, x_44, x_42);
lean_dec(x_44);
x_46 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5(x_4, x_5, x_21, x_23, x_6, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_45, x_15, x_16, x_17, x_18, x_43);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
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
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
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
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after introN\n", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_array_get_size(x_1);
x_19 = lean_box(0);
x_20 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_18);
x_21 = l_Lean_Meta_introNCore(x_2, x_18, x_19, x_20, x_20, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_3);
x_27 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_13, x_14, x_15, x_16, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_22);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_25, x_4, x_26, x_5, x_6, x_3, x_19, x_7, x_8, x_9, x_18, x_10, x_11, x_31, x_13, x_14, x_15, x_16, x_30);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
lean_inc(x_26);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_26);
x_37 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_37);
x_38 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_38);
lean_ctor_set(x_22, 0, x_27);
lean_inc(x_3);
x_39 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_22, x_13, x_14, x_15, x_16, x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_25, x_4, x_26, x_5, x_6, x_3, x_19, x_7, x_8, x_9, x_18, x_10, x_11, x_40, x_13, x_14, x_15, x_16, x_41);
lean_dec(x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
lean_inc(x_26);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_26);
x_45 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_47);
lean_ctor_set(x_22, 0, x_46);
lean_inc(x_3);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_22, x_13, x_14, x_15, x_16, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_25, x_4, x_26, x_5, x_6, x_3, x_19, x_7, x_8, x_9, x_18, x_10, x_11, x_49, x_13, x_14, x_15, x_16, x_50);
lean_dec(x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
lean_inc(x_3);
x_54 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_13, x_14, x_15, x_16, x_23);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_52, x_4, x_53, x_5, x_6, x_3, x_19, x_7, x_8, x_9, x_18, x_10, x_11, x_58, x_13, x_14, x_15, x_16, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
lean_inc(x_53);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_53);
x_63 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2;
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_61;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_3);
x_67 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_66, x_13, x_14, x_15, x_16, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_52, x_4, x_53, x_5, x_6, x_3, x_19, x_7, x_8, x_9, x_18, x_10, x_11, x_68, x_13, x_14, x_15, x_16, x_69);
lean_dec(x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
return x_21;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalize\n", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_size(x_1);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_19, x_20, x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_22 = l_Lean_Meta_generalizeTargetsEq(x_2, x_3, x_21, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1;
lean_inc(x_5);
lean_inc(x_4);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lambda__1___boxed), 8, 3);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_5);
lean_closure_set(x_26, 2, x_25);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_23);
x_27 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_23, x_26, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_4);
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_14, x_15, x_16, x_17, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8(x_6, x_23, x_4, x_20, x_7, x_8, x_9, x_10, x_5, x_11, x_12, x_33, x_14, x_15, x_16, x_17, x_32);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_29, 1);
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
lean_inc(x_23);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_23);
x_39 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_38);
lean_ctor_set(x_29, 0, x_39);
x_40 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_4);
x_42 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_41, x_14, x_15, x_16, x_17, x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8(x_6, x_23, x_4, x_20, x_7, x_8, x_9, x_10, x_5, x_11, x_12, x_43, x_14, x_15, x_16, x_17, x_44);
lean_dec(x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
lean_inc(x_23);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_23);
x_48 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_4);
x_52 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_51, x_14, x_15, x_16, x_17, x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8(x_6, x_23, x_4, x_20, x_7, x_8, x_9, x_10, x_5, x_11, x_12, x_53, x_14, x_15, x_16, x_17, x_54);
lean_dec(x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_22);
if (x_60 == 0)
{
return x_22;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_22, 0);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_22);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalizeMatchDiscrs\n", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(x_1, x_2, x_3, x_4, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_5);
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_5, x_12, x_13, x_14, x_15, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_19);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_21, x_24, x_3, x_5, x_23, x_4, x_6, x_7, x_8, x_9, x_2, x_10, x_29, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_4);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
lean_inc(x_24);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_24);
x_35 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
x_36 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_36);
lean_ctor_set(x_19, 0, x_25);
lean_inc(x_5);
x_37 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_5, x_19, x_12, x_13, x_14, x_15, x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_21, x_24, x_3, x_5, x_23, x_4, x_6, x_7, x_8, x_9, x_2, x_10, x_38, x_12, x_13, x_14, x_15, x_39);
lean_dec(x_38);
lean_dec(x_4);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_dec(x_25);
lean_inc(x_24);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_24);
x_43 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_45);
lean_ctor_set(x_19, 0, x_44);
lean_inc(x_5);
x_46 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_5, x_19, x_12, x_13, x_14, x_15, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_21, x_24, x_3, x_5, x_23, x_4, x_6, x_7, x_8, x_9, x_2, x_10, x_47, x_12, x_13, x_14, x_15, x_48);
lean_dec(x_47);
lean_dec(x_4);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
lean_inc(x_5);
x_52 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_5, x_12, x_13, x_14, x_15, x_20);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_21, x_51, x_3, x_5, x_50, x_4, x_6, x_7, x_8, x_9, x_2, x_10, x_56, x_12, x_13, x_14, x_15, x_55);
lean_dec(x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
lean_inc(x_51);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_51);
x_61 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2;
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(7, 2, 0);
} else {
 x_62 = x_59;
 lean_ctor_set_tag(x_62, 7);
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_5);
x_65 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_5, x_64, x_12, x_13, x_14, x_15, x_58);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_21, x_51, x_3, x_5, x_50, x_4, x_6, x_7, x_8, x_9, x_2, x_10, x_66, x_12, x_13, x_14, x_15, x_67);
lean_dec(x_66);
lean_dec(x_4);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_17);
if (x_69 == 0)
{
return x_17;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_17, 0);
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_17);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: `", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not an auxiliary declaration used to encode `match`-expressions\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 176, 176);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("applyMatchSplitter\n", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l_Lean_MessageData_ofName(x_2);
x_17 = l_Lean_Meta_Split_applyMatchSplitter___closed__2;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_16);
lean_ctor_set(x_11, 0, x_17);
x_18 = l_Lean_Meta_Split_applyMatchSplitter___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_19, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_MessageData_ofName(x_2);
x_23 = l_Lean_Meta_Split_applyMatchSplitter___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_Split_applyMatchSplitter___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_26, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_11, 1);
x_30 = lean_ctor_get(x_11, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_33 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_inc(x_3);
x_37 = lean_array_to_list(x_3);
lean_inc(x_36);
x_38 = l_Lean_Expr_const___override(x_36, x_37);
x_39 = l_Lean_mkAppN(x_38, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = lean_infer_type(x_39, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_whnfForall(x_41, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_bindingDomain_x21(x_44);
lean_dec(x_44);
x_47 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_48 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_47, x_6, x_7, x_8, x_9, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_12);
lean_free_object(x_11);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_46, x_5, x_47, x_36, x_4, x_32, x_34, x_3, x_52, x_6, x_7, x_8, x_9, x_51);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_48, 1);
x_56 = lean_ctor_get(x_48, 0);
lean_dec(x_56);
lean_inc(x_1);
lean_ctor_set(x_12, 0, x_1);
x_57 = l_Lean_Meta_Split_applyMatchSplitter___closed__6;
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 0, x_57);
x_58 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_58);
lean_ctor_set(x_11, 0, x_48);
x_59 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_11, x_6, x_7, x_8, x_9, x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_46, x_5, x_47, x_36, x_4, x_32, x_34, x_3, x_60, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_dec(x_48);
lean_inc(x_1);
lean_ctor_set(x_12, 0, x_1);
x_64 = l_Lean_Meta_Split_applyMatchSplitter___closed__6;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
x_66 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_66);
lean_ctor_set(x_11, 0, x_65);
x_67 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_47, x_11, x_6, x_7, x_8, x_9, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_46, x_5, x_47, x_36, x_4, x_32, x_34, x_3, x_68, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_36);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
return x_43;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_43, 0);
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_43);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_36);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_40, 0);
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_40);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_12);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_33);
if (x_79 == 0)
{
return x_33;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_33, 0);
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_33);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_84 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_inc(x_3);
x_88 = lean_array_to_list(x_3);
lean_inc(x_87);
x_89 = l_Lean_Expr_const___override(x_87, x_88);
x_90 = l_Lean_mkAppN(x_89, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_91 = lean_infer_type(x_90, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_94 = l_Lean_Meta_whnfForall(x_92, x_6, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_bindingDomain_x21(x_95);
lean_dec(x_95);
x_98 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_98, x_6, x_7, x_8, x_9, x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_11);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
x_104 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_97, x_5, x_98, x_87, x_4, x_83, x_85, x_3, x_103, x_6, x_7, x_8, x_9, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
lean_inc(x_1);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_1);
x_108 = l_Lean_Meta_Split_applyMatchSplitter___closed__6;
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_106;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_110);
lean_ctor_set(x_11, 0, x_109);
x_111 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_98, x_11, x_6, x_7, x_8, x_9, x_105);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_97, x_5, x_98, x_87, x_4, x_83, x_85, x_3, x_112, x_6, x_7, x_8, x_9, x_113);
lean_dec(x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_83);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_ctor_get(x_94, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_94, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_117 = x_94;
} else {
 lean_dec_ref(x_94);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_83);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_91, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_91, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_121 = x_91;
} else {
 lean_dec_ref(x_91);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_83);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_84, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_84, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_125 = x_84;
} else {
 lean_dec_ref(x_84);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_11, 1);
lean_inc(x_127);
lean_dec(x_11);
x_128 = lean_ctor_get(x_12, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_129 = x_12;
} else {
 lean_dec_ref(x_12);
 x_129 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_130 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_inc(x_3);
x_134 = lean_array_to_list(x_3);
lean_inc(x_133);
x_135 = l_Lean_Expr_const___override(x_133, x_134);
x_136 = l_Lean_mkAppN(x_135, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_137 = lean_infer_type(x_136, x_6, x_7, x_8, x_9, x_132);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_140 = l_Lean_Meta_whnfForall(x_138, x_6, x_7, x_8, x_9, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Expr_bindingDomain_x21(x_141);
lean_dec(x_141);
x_144 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_145 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_144, x_6, x_7, x_8, x_9, x_142);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_129);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_box(0);
x_150 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_143, x_5, x_144, x_133, x_4, x_128, x_131, x_3, x_149, x_6, x_7, x_8, x_9, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_129)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_129;
}
lean_ctor_set(x_153, 0, x_1);
x_154 = l_Lean_Meta_Split_applyMatchSplitter___closed__6;
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_152;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_144, x_157, x_6, x_7, x_8, x_9, x_151);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_143, x_5, x_144, x_133, x_4, x_128, x_131, x_3, x_159, x_6, x_7, x_8, x_9, x_160);
lean_dec(x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_140, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_140, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_164 = x_140;
} else {
 lean_dec_ref(x_140);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_137, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_137, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_168 = x_137;
} else {
 lean_dec_ref(x_137);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_130, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_130, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_172 = x_130;
} else {
 lean_dec_ref(x_130);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_Split_applyMatchSplitter___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___boxed(lean_object** _args) {
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
x_18 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Split_applyMatchSplitter___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___boxed(lean_object** _args) {
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
size_t x_20; lean_object* x_21; 
x_20 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_21 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
lean_dec(x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__8___boxed(lean_object** _args) {
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
size_t x_18; lean_object* x_19; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = l_Lean_Meta_Split_applyMatchSplitter___lambda__8(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Lean_Meta_Split_applyMatchSplitter___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Split_applyMatchSplitter___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Split_applyMatchSplitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed to generalize discriminant(s) at", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nresulting expression was not type correct\npossible solution: generalize discriminant(s) manually before using `split`", 118, 118);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_indentExpr(x_1);
x_3 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_1);
x_8 = l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Split_throwDiscrGenError___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Split_throwDiscrGenError___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Split_throwDiscrGenError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_Lean_instInhabitedName;
x_19 = lean_array_get(x_18, x_17, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_13, x_1, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_15, x_23);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_21);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_24);
x_4 = x_14;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
x_35 = l_Lean_instInhabitedName;
x_36 = lean_array_get(x_35, x_34, x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_30, x_1, x_36, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_32, x_40);
lean_dec(x_32);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
x_3 = x_42;
x_4 = x_31;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_4);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_52 = x_3;
} else {
 lean_dec_ref(x_3);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_2, 0);
x_54 = l_Lean_instInhabitedName;
x_55 = lean_array_get(x_54, x_53, x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_56 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_48, x_1, x_55, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_50, x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_51);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_3 = x_62;
x_4 = x_49;
x_9 = x_58;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: match application expected", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_splitMatch___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 108, 108);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_splitMatch___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_indentExpr(x_1);
x_13 = l_Lean_Meta_Split_splitMatch___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Split_splitMatch___lambda__1___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_16, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
x_21 = lean_get_match_equations_for(x_20, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 6);
lean_inc(x_26);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
x_27 = l_Lean_Meta_Split_applyMatchSplitter(x_2, x_20, x_24, x_25, x_26, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Split_splitMatch___lambda__1___closed__5;
x_31 = l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(x_20, x_22, x_30, x_28, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_22);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_List_reverse___rarg(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_List_reverse___rarg(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
return x_9;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Split_splitMatch___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Expr_hash(x_2);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_14, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_13, x_30);
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_array_uset(x_14, x_27, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_31, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_34);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_31);
x_42 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11);
return x_42;
}
else
{
lean_object* x_43; 
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_31);
x_43 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_28);
lean_dec(x_2);
x_44 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_47 = lean_array_get_size(x_46);
x_48 = l_Lean_Expr_hash(x_2);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_46, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_45, x_62);
lean_dec(x_45);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_60);
x_66 = lean_array_uset(x_46, x_59, x_65);
x_67 = lean_unsigned_to_nat(4u);
x_68 = lean_nat_mul(x_63, x_67);
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_div(x_68, x_69);
lean_dec(x_68);
x_71 = lean_array_get_size(x_66);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_63);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_74, x_7, x_8, x_9, x_10, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_66);
x_77 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_76, x_7, x_8, x_9, x_10, x_11);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_60);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_45);
lean_ctor_set(x_78, 1, x_46);
x_79 = l_Lean_Meta_splitTarget_x3f_go(x_3, x_4, x_5, x_78, x_7, x_8, x_9, x_10, x_11);
return x_79;
}
}
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find term to split\n", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failure", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1;
x_2 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed at", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
if (x_2 == 0)
{
uint8_t x_369; 
x_369 = 1;
x_10 = x_369;
goto block_368;
}
else
{
uint8_t x_370; 
x_370 = 2;
x_10 = x_370;
goto block_368;
}
block_368:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_findSplit_x3f(x_3, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_5, x_6, x_7, x_8, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1;
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_15);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_apply_6(x_19, x_21, x_5, x_6, x_7, x_8, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_Meta_splitTarget_x3f_go___closed__2;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set(x_15, 0, x_24);
x_25 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_26, x_5, x_6, x_7, x_8, x_18);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_apply_6(x_19, x_28, x_5, x_6, x_7, x_8, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1;
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_apply_6(x_33, x_35, x_5, x_6, x_7, x_8, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = l_Lean_Meta_splitTarget_x3f_go___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_41, x_5, x_6, x_7, x_8, x_32);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_6(x_33, x_43, x_5, x_6, x_7, x_8, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = l_Lean_Expr_isIte(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_isDIte(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_48);
lean_inc(x_1);
x_51 = l_Lean_Meta_Split_splitMatch(x_1, x_48, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_12, 0, x_53);
lean_ctor_set(x_51, 0, x_12);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_12, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_12);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
x_60 = l_Lean_Exception_isInterrupt(x_58);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Exception_isRuntime(x_58);
if (x_61 == 0)
{
uint8_t x_62; 
lean_free_object(x_51);
x_62 = l_Lean_Meta_Split_isDiscrGenException(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_64 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_63, x_5, x_6, x_7, x_8, x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_58);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_68, x_5, x_6, x_7, x_8, x_67);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_64, 1);
x_72 = lean_ctor_get(x_64, 0);
lean_dec(x_72);
lean_inc(x_48);
x_73 = l_Lean_indentExpr(x_48);
x_74 = l_Lean_Meta_splitTarget_x3f_go___closed__6;
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_73);
lean_ctor_set(x_64, 0, x_74);
x_75 = l_Lean_Meta_splitTarget_x3f_go___closed__8;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Exception_toMessageData(x_58);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_63, x_80, x_5, x_6, x_7, x_8, x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_82, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_85 = lean_ctor_get(x_64, 1);
lean_inc(x_85);
lean_dec(x_64);
lean_inc(x_48);
x_86 = l_Lean_indentExpr(x_48);
x_87 = l_Lean_Meta_splitTarget_x3f_go___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Meta_splitTarget_x3f_go___closed__8;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Exception_toMessageData(x_58);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_63, x_94, x_5, x_6, x_7, x_8, x_85);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_96, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_58);
x_99 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_100 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_99, x_5, x_6, x_7, x_8, x_59);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_104, x_5, x_6, x_7, x_8, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec(x_100);
lean_inc(x_48);
x_107 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_48);
x_108 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_99, x_107, x_5, x_6, x_7, x_8, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_109, x_5, x_6, x_7, x_8, x_110);
lean_dec(x_109);
return x_111;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_51;
}
}
else
{
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_51;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_51, 0);
x_113 = lean_ctor_get(x_51, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_51);
x_114 = l_Lean_Exception_isInterrupt(x_112);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = l_Lean_Exception_isRuntime(x_112);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Meta_Split_isDiscrGenException(x_112);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_118 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_117, x_5, x_6, x_7, x_8, x_113);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_112);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_box(0);
x_123 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_122, x_5, x_6, x_7, x_8, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
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
lean_inc(x_48);
x_126 = l_Lean_indentExpr(x_48);
x_127 = l_Lean_Meta_splitTarget_x3f_go___closed__6;
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(7, 2, 0);
} else {
 x_128 = x_125;
 lean_ctor_set_tag(x_128, 7);
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Meta_splitTarget_x3f_go___closed__8;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Exception_toMessageData(x_112);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_117, x_134, x_5, x_6, x_7, x_8, x_124);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_136, x_5, x_6, x_7, x_8, x_137);
lean_dec(x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_112);
x_139 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_140 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_139, x_5, x_6, x_7, x_8, x_113);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_box(0);
x_145 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_144, x_5, x_6, x_7, x_8, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
lean_inc(x_48);
x_147 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_48);
x_148 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_139, x_147, x_5, x_6, x_7, x_8, x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_48, x_1, x_2, x_3, x_149, x_5, x_6, x_7, x_8, x_150);
lean_dec(x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_112);
lean_ctor_set(x_152, 1, x_113);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_112);
lean_ctor_set(x_153, 1, x_113);
return x_153;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_free_object(x_12);
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_box(0);
x_155 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_154, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_155);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_155, 0);
lean_dec(x_158);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_156);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_156, 0);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = !lean_is_exclusive(x_155);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_155, 0);
lean_dec(x_166);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_163, 1);
lean_dec(x_168);
x_169 = !lean_is_exclusive(x_164);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_164, 1);
lean_dec(x_170);
x_171 = lean_box(0);
lean_ctor_set_tag(x_164, 1);
lean_ctor_set(x_164, 1, x_171);
lean_ctor_set_tag(x_163, 1);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_156, 0, x_163);
return x_155;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_164, 0);
lean_inc(x_172);
lean_dec(x_164);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set_tag(x_163, 1);
lean_ctor_set(x_163, 1, x_174);
lean_ctor_set(x_156, 0, x_163);
return x_155;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_163, 0);
lean_inc(x_175);
lean_dec(x_163);
x_176 = lean_ctor_get(x_164, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_177 = x_164;
} else {
 lean_dec_ref(x_164);
 x_177 = lean_box(0);
}
x_178 = lean_box(0);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_177;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_156, 0, x_180);
return x_155;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_181 = lean_ctor_get(x_155, 1);
lean_inc(x_181);
lean_dec(x_155);
x_182 = lean_ctor_get(x_163, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_183 = x_163;
} else {
 lean_dec_ref(x_163);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_164, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_185 = x_164;
} else {
 lean_dec_ref(x_164);
 x_185 = lean_box(0);
}
x_186 = lean_box(0);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_185;
 lean_ctor_set_tag(x_187, 1);
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_183;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_182);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_156, 0, x_188);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_156);
lean_ctor_set(x_189, 1, x_181);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_190 = lean_ctor_get(x_156, 0);
lean_inc(x_190);
lean_dec(x_156);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_155, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_194 = x_155;
} else {
 lean_dec_ref(x_155);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_191, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_196 = x_191;
} else {
 lean_dec_ref(x_191);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_198;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_199);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_196;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
if (lean_is_scalar(x_194)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_194;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_193);
return x_203;
}
}
}
else
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_155);
if (x_204 == 0)
{
return x_155;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_155, 0);
x_206 = lean_ctor_get(x_155, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_155);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_free_object(x_12);
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_3);
x_208 = lean_box(0);
x_209 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_208, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_209);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_209, 0);
lean_dec(x_212);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_dec(x_209);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_210);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_ctor_get(x_210, 0);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = !lean_is_exclusive(x_209);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_209, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_217);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_217, 1);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_218);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_218, 1);
lean_dec(x_224);
x_225 = lean_box(0);
lean_ctor_set_tag(x_218, 1);
lean_ctor_set(x_218, 1, x_225);
lean_ctor_set_tag(x_217, 1);
lean_ctor_set(x_217, 1, x_218);
lean_ctor_set(x_210, 0, x_217);
return x_209;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_218, 0);
lean_inc(x_226);
lean_dec(x_218);
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set_tag(x_217, 1);
lean_ctor_set(x_217, 1, x_228);
lean_ctor_set(x_210, 0, x_217);
return x_209;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_ctor_get(x_217, 0);
lean_inc(x_229);
lean_dec(x_217);
x_230 = lean_ctor_get(x_218, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_231 = x_218;
} else {
 lean_dec_ref(x_218);
 x_231 = lean_box(0);
}
x_232 = lean_box(0);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_231;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_210, 0, x_234);
return x_209;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_235 = lean_ctor_get(x_209, 1);
lean_inc(x_235);
lean_dec(x_209);
x_236 = lean_ctor_get(x_217, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_237 = x_217;
} else {
 lean_dec_ref(x_217);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_218, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_239 = x_218;
} else {
 lean_dec_ref(x_218);
 x_239 = lean_box(0);
}
x_240 = lean_box(0);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_239;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_240);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_237;
 lean_ctor_set_tag(x_242, 1);
}
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set(x_210, 0, x_242);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_210);
lean_ctor_set(x_243, 1, x_235);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_244 = lean_ctor_get(x_210, 0);
lean_inc(x_244);
lean_dec(x_210);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_209, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_248 = x_209;
} else {
 lean_dec_ref(x_209);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_245, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_246, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_252 = x_246;
} else {
 lean_dec_ref(x_246);
 x_252 = lean_box(0);
}
x_253 = lean_box(0);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_252;
 lean_ctor_set_tag(x_254, 1);
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_250;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
if (lean_is_scalar(x_248)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_248;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_247);
return x_257;
}
}
}
else
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_209);
if (x_258 == 0)
{
return x_209;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_209, 0);
x_260 = lean_ctor_get(x_209, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_209);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
else
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_12, 0);
lean_inc(x_262);
lean_dec(x_12);
x_263 = l_Lean_Expr_isIte(x_262);
if (x_263 == 0)
{
uint8_t x_264; 
x_264 = l_Lean_Expr_isDIte(x_262);
if (x_264 == 0)
{
lean_object* x_265; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_262);
lean_inc(x_1);
x_265 = l_Lean_Meta_Split_splitMatch(x_1, x_262, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_262);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_266);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_265, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
x_274 = l_Lean_Exception_isInterrupt(x_271);
if (x_274 == 0)
{
uint8_t x_275; 
x_275 = l_Lean_Exception_isRuntime(x_271);
if (x_275 == 0)
{
uint8_t x_276; 
lean_dec(x_273);
x_276 = l_Lean_Meta_Split_isDiscrGenException(x_271);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_277 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_278 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_277, x_5, x_6, x_7, x_8, x_272);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_271);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = lean_box(0);
x_283 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_262, x_1, x_2, x_3, x_282, x_5, x_6, x_7, x_8, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
 x_285 = lean_box(0);
}
lean_inc(x_262);
x_286 = l_Lean_indentExpr(x_262);
x_287 = l_Lean_Meta_splitTarget_x3f_go___closed__6;
if (lean_is_scalar(x_285)) {
 x_288 = lean_alloc_ctor(7, 2, 0);
} else {
 x_288 = x_285;
 lean_ctor_set_tag(x_288, 7);
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = l_Lean_Meta_splitTarget_x3f_go___closed__8;
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Lean_Exception_toMessageData(x_271);
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9;
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_277, x_294, x_5, x_6, x_7, x_8, x_284);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_262, x_1, x_2, x_3, x_296, x_5, x_6, x_7, x_8, x_297);
lean_dec(x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_dec(x_271);
x_299 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_300 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_299, x_5, x_6, x_7, x_8, x_272);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_unbox(x_301);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_box(0);
x_305 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_262, x_1, x_2, x_3, x_304, x_5, x_6, x_7, x_8, x_303);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_300, 1);
lean_inc(x_306);
lean_dec(x_300);
lean_inc(x_262);
x_307 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_262);
x_308 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_299, x_307, x_5, x_6, x_7, x_8, x_306);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_4, x_262, x_1, x_2, x_3, x_309, x_5, x_6, x_7, x_8, x_310);
lean_dec(x_309);
return x_311;
}
}
}
else
{
lean_object* x_312; 
lean_dec(x_262);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_273)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_273;
}
lean_ctor_set(x_312, 0, x_271);
lean_ctor_set(x_312, 1, x_272);
return x_312;
}
}
else
{
lean_object* x_313; 
lean_dec(x_262);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_273)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_273;
}
lean_ctor_set(x_313, 0, x_271);
lean_ctor_set(x_313, 1, x_272);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_262);
lean_dec(x_4);
lean_dec(x_3);
x_314 = lean_box(0);
x_315 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_314, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_314);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_320 = lean_ctor_get(x_316, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_321 = x_316;
} else {
 lean_dec_ref(x_316);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_ctor_get(x_315, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_325 = x_315;
} else {
 lean_dec_ref(x_315);
 x_325 = lean_box(0);
}
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_327 = x_322;
} else {
 lean_dec_ref(x_322);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_329 = x_323;
} else {
 lean_dec_ref(x_323);
 x_329 = lean_box(0);
}
x_330 = lean_box(0);
if (lean_is_scalar(x_329)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_329;
 lean_ctor_set_tag(x_331, 1);
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_330);
if (lean_is_scalar(x_327)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_327;
 lean_ctor_set_tag(x_332, 1);
}
lean_ctor_set(x_332, 0, x_326);
lean_ctor_set(x_332, 1, x_331);
if (lean_is_scalar(x_321)) {
 x_333 = lean_alloc_ctor(1, 1, 0);
} else {
 x_333 = x_321;
}
lean_ctor_set(x_333, 0, x_332);
if (lean_is_scalar(x_325)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_325;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_324);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_ctor_get(x_315, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_315, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_337 = x_315;
} else {
 lean_dec_ref(x_315);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_262);
lean_dec(x_4);
lean_dec(x_3);
x_339 = lean_box(0);
x_340 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_339, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_339);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_346 = x_341;
} else {
 lean_dec_ref(x_341);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_ctor_get(x_340, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_350 = x_340;
} else {
 lean_dec_ref(x_340);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_347, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_348, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_354 = x_348;
} else {
 lean_dec_ref(x_348);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_354;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_355);
if (lean_is_scalar(x_352)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_352;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_356);
if (lean_is_scalar(x_346)) {
 x_358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_358 = x_346;
}
lean_ctor_set(x_358, 0, x_357);
if (lean_is_scalar(x_350)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_350;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_349);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_340, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_340, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_362 = x_340;
} else {
 lean_dec_ref(x_340);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
}
}
}
else
{
uint8_t x_364; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_364 = !lean_is_exclusive(x_11);
if (x_364 == 0)
{
return x_11;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_11, 0);
x_366 = lean_ctor_get(x_11, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_11);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_23; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_23, 0, x_37);
return x_23;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_40 = x_24;
} else {
 lean_dec_ref(x_24);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_dec(x_23);
x_11 = x_43;
x_12 = x_44;
goto block_22;
}
block_22:
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isInterrupt(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Exception_isRuntime(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_10);
x_15 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_10)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_10;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_10)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_10;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3;
x_15 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_2, x_12, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_splitTarget_x3f___lambda__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_splitTarget_x3f___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_splitTarget_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = l_List_reverse___rarg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_box(0);
x_15 = 0;
x_16 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Meta_introNCore(x_12, x_1, x_14, x_15, x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_20);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_19;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = 0;
x_30 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_31 = l_Lean_Meta_introNCore(x_26, x_1, x_28, x_29, x_30, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
x_2 = x_27;
x_3 = x_35;
x_8 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_intro1Core(x_11, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_16;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_intro1Core(x_23, x_25, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
x_1 = x_24;
x_2 = x_30;
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_21; lean_object* x_22; 
x_21 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_MVarId_revert(x_1, x_2, x_21, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_get_size(x_25);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Meta_Split_splitMatch(x_26, x_3, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_27, x_29, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_10 = x_39;
x_11 = x_40;
goto block_20;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
x_10 = x_41;
x_11 = x_42;
goto block_20;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_dec(x_22);
x_10 = x_43;
x_11 = x_44;
goto block_20;
}
block_20:
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isInterrupt(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_Split_isDiscrGenException(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_throwDiscrGenError___rarg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_FVarId_getDecl(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_MVarId_getType(x_2, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_isLet(x_12);
if (x_18 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Lean_exprDependsOn___at___private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go___spec__1(x_15, x_1, x_6, x_7, x_8, x_9, x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_inc(x_6);
x_64 = l_Lean_FVarId_hasForwardDeps(x_1, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_19 = x_67;
x_20 = x_66;
goto block_59;
}
else
{
uint8_t x_68; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_unbox(x_61);
lean_dec(x_61);
x_19 = x_73;
x_20 = x_72;
goto block_59;
}
}
else
{
lean_dec(x_15);
lean_dec(x_1);
x_19 = x_18;
x_20 = x_16;
goto block_59;
}
block_59:
{
if (x_19 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_21 = l_Lean_Meta_Split_throwDiscrGenError___rarg(x_3, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_39; 
x_22 = l_Lean_LocalDecl_userName(x_12);
x_23 = l_Lean_LocalDecl_type(x_12);
x_24 = l_Lean_LocalDecl_toExpr(x_12);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_MVarId_assert(x_2, x_22, x_23, x_24, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_42 = l_Lean_Meta_Split_splitMatch(x_40, x_3, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_List_mapM_loop___at_Lean_Meta_splitLocalDecl_x3f___spec__2(x_43, x_4, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_25 = x_53;
x_26 = x_54;
goto block_38;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_dec(x_42);
x_25 = x_55;
x_26 = x_56;
goto block_38;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_25 = x_57;
x_26 = x_58;
goto block_38;
}
block_38:
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isInterrupt(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Exception_isRuntime(x_25);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Meta_Split_isDiscrGenException(x_25);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_is_scalar(x_17)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_17;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_17);
x_31 = l_Lean_Meta_Split_throwDiscrGenError___rarg(x_3, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
lean_object* x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_is_scalar(x_17)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_17;
 lean_ctor_set_tag(x_36, 1);
}
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_is_scalar(x_17)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_17;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_14);
if (x_74 == 0)
{
return x_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_11);
if (x_78 == 0)
{
return x_11;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_11, 0);
x_80 = lean_ctor_get(x_11, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_11);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_10, x_4, x_5, x_6, x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = 2;
x_17 = l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_findSplit_x3f(x_14, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_Expr_isIte(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isDIte(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_box(0);
lean_inc(x_2);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_2);
x_31 = lean_array_mk(x_12);
lean_inc(x_27);
lean_inc(x_3);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lambda__1), 9, 4);
lean_closure_set(x_32, 0, x_3);
lean_closure_set(x_32, 1, x_31);
lean_closure_set(x_32, 2, x_27);
lean_closure_set(x_32, 3, x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(x_32, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_splitLocalDecl_x3f___lambda__3(x_2, x_3, x_27, x_30, x_36, x_4, x_5, x_6, x_7, x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_splitIfLocalDecl_x3f(x_3, x_2, x_46, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_free_object(x_12);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_47, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = lean_box(0);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 1, x_60);
lean_ctor_set(x_55, 0, x_59);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_55);
lean_ctor_set(x_12, 0, x_58);
lean_ctor_set(x_48, 0, x_12);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_64);
lean_ctor_set(x_12, 0, x_61);
lean_ctor_set(x_48, 0, x_12);
return x_47;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_48, 0);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_dec(x_47);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_69;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_71);
lean_ctor_set(x_12, 0, x_67);
lean_ctor_set(x_48, 0, x_12);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_48, 0);
lean_inc(x_73);
lean_dec(x_48);
x_74 = lean_ctor_get(x_47, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_75 = x_47;
} else {
 lean_dec_ref(x_47);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_78;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_80);
lean_ctor_set(x_12, 0, x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_12);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_12);
x_83 = !lean_is_exclusive(x_47);
if (x_83 == 0)
{
return x_47;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_47, 0);
x_85 = lean_ctor_get(x_47, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_47);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_27);
x_87 = lean_box(0);
x_88 = l_Lean_Meta_splitIfLocalDecl_x3f(x_3, x_2, x_87, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_free_object(x_12);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
x_101 = lean_box(0);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_101);
lean_ctor_set(x_96, 0, x_100);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_96);
lean_ctor_set(x_12, 0, x_99);
lean_ctor_set(x_89, 0, x_12);
return x_88;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_105);
lean_ctor_set(x_12, 0, x_102);
lean_ctor_set(x_89, 0, x_12);
return x_88;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_89, 0);
x_107 = lean_ctor_get(x_88, 1);
lean_inc(x_107);
lean_dec(x_88);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = lean_box(0);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_110;
 lean_ctor_set_tag(x_112, 1);
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_112);
lean_ctor_set(x_12, 0, x_108);
lean_ctor_set(x_89, 0, x_12);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_89);
lean_ctor_set(x_113, 1, x_107);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_89, 0);
lean_inc(x_114);
lean_dec(x_89);
x_115 = lean_ctor_get(x_88, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_116 = x_88;
} else {
 lean_dec_ref(x_88);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_119;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_121);
lean_ctor_set(x_12, 0, x_117);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_12);
if (lean_is_scalar(x_116)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_116;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_12);
x_124 = !lean_is_exclusive(x_88);
if (x_124 == 0)
{
return x_88;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_88, 0);
x_126 = lean_ctor_get(x_88, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_88);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_18);
if (x_128 == 0)
{
return x_18;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_18, 0);
x_130 = lean_ctor_get(x_18, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_18);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_12, 0);
x_133 = lean_ctor_get(x_12, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_12);
x_134 = 2;
x_135 = l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_136 = l_Lean_Meta_findSplit_x3f(x_132, x_134, x_135, x_4, x_5, x_6, x_7, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_box(0);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
lean_dec(x_137);
x_144 = l_Lean_Expr_isIte(x_143);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = l_Lean_Expr_isDIte(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_box(0);
lean_inc(x_2);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_2);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_mk(x_147);
lean_inc(x_143);
lean_inc(x_3);
x_149 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lambda__1), 9, 4);
lean_closure_set(x_149, 0, x_3);
lean_closure_set(x_149, 1, x_148);
lean_closure_set(x_149, 2, x_143);
lean_closure_set(x_149, 3, x_146);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_150 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(x_149, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_box(0);
x_154 = l_Lean_Meta_splitLocalDecl_x3f___lambda__3(x_2, x_3, x_143, x_146, x_153, x_4, x_5, x_6, x_7, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_143);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_156 = x_150;
} else {
 lean_dec_ref(x_150);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_143);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_143);
x_162 = lean_box(0);
x_163 = l_Lean_Meta_splitIfLocalDecl_x3f(x_3, x_2, x_162, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_163, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_171 = x_163;
} else {
 lean_dec_ref(x_163);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_174;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_169)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_169;
}
lean_ctor_set(x_178, 0, x_177);
if (lean_is_scalar(x_171)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_171;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_163, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_163, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_182 = x_163;
} else {
 lean_dec_ref(x_163);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_143);
x_184 = lean_box(0);
x_185 = l_Lean_Meta_splitIfLocalDecl_x3f(x_3, x_2, x_184, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_185, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_193 = x_185;
} else {
 lean_dec_ref(x_185);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
 x_196 = lean_box(0);
}
x_197 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_196;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_198);
if (lean_is_scalar(x_191)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_191;
}
lean_ctor_set(x_200, 0, x_199);
if (lean_is_scalar(x_193)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_193;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_192);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_185, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_185, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_204 = x_185;
} else {
 lean_dec_ref(x_185);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_206 = lean_ctor_get(x_136, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_136, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_208 = x_136;
} else {
 lean_dec_ref(x_136);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_9);
if (x_210 == 0)
{
return x_9;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_9, 0);
x_212 = lean_ctor_get(x_9, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_9);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lambda__4), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_splitLocalDecl_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_splitLocalDecl_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16;
x_2 = lean_unsigned_to_nat(6812u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Split_getSimpMatchContext___closed__1 = _init_l_Lean_Meta_Split_getSimpMatchContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_getSimpMatchContext___closed__1);
l_Lean_Meta_Split_getSimpMatchContext___closed__2 = _init_l_Lean_Meta_Split_getSimpMatchContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_getSimpMatchContext___closed__2);
l_Lean_Meta_Split_simpMatch_pre___closed__1 = _init_l_Lean_Meta_Split_simpMatch_pre___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch_pre___closed__1);
l_Lean_Meta_Split_simpMatch___lambda__2___closed__1 = _init_l_Lean_Meta_Split_simpMatch___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___lambda__2___closed__1);
l_Lean_Meta_Split_simpMatch___closed__1 = _init_l_Lean_Meta_Split_simpMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__1);
l_Lean_Meta_Split_simpMatch___closed__2 = _init_l_Lean_Meta_Split_simpMatch___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__2);
l_Lean_Meta_Split_simpMatch___closed__3 = _init_l_Lean_Meta_Split_simpMatch___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__3);
l_Lean_Meta_Split_simpMatch___closed__4 = _init_l_Lean_Meta_Split_simpMatch___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__4);
l_Lean_Meta_Split_simpMatch___closed__5 = _init_l_Lean_Meta_Split_simpMatch___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__5);
l_Lean_Meta_Split_simpMatch___closed__6 = _init_l_Lean_Meta_Split_simpMatch___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__6);
l_Lean_Meta_Split_simpMatch___closed__7 = _init_l_Lean_Meta_Split_simpMatch___closed__7();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__7);
l_Lean_Meta_Split_simpMatch___closed__8 = _init_l_Lean_Meta_Split_simpMatch___closed__8();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__8);
l_Lean_Meta_Split_simpMatch___closed__9 = _init_l_Lean_Meta_Split_simpMatch___closed__9();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__9);
l_Lean_Meta_Split_simpMatch___closed__10 = _init_l_Lean_Meta_Split_simpMatch___closed__10();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__10);
l_Lean_Meta_Split_simpMatch___closed__11 = _init_l_Lean_Meta_Split_simpMatch___closed__11();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__11);
l_Lean_Meta_Split_simpMatch___closed__12 = _init_l_Lean_Meta_Split_simpMatch___closed__12();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__12);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__2();
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___rarg___closed__2);
l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1 = _init_l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1();
lean_mark_persistent(l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__1);
l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2 = _init_l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2();
lean_mark_persistent(l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920____closed__2);
if (builtin) {res = l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_920_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Split_discrGenExId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Split_discrGenExId);
lean_dec_ref(res);
}l_Lean_Meta_Split_isDiscrGenException___closed__1 = _init_l_Lean_Meta_Split_isDiscrGenException___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_isDiscrGenException___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__6);
l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__2___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__2);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__3);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__3___closed__4);
l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1 = _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__2___closed__1);
l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1 = _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___lambda__3___closed__1);
l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1 = _init_l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__2);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__3);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__4);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__5);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__6);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__7);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__8);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__5___closed__9);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__6___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__3);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__4);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lambda__6___closed__5);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__1);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__2___closed__2);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__1___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__4);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__5);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__6);
l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__3___closed__7);
l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__4);
l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__8___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__9___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__9___boxed__const__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__10___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__4);
l_Lean_Meta_Split_applyMatchSplitter___closed__5 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__5);
l_Lean_Meta_Split_applyMatchSplitter___closed__6 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__6);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__4);
l_Lean_Meta_Split_splitMatch___lambda__1___closed__1 = _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lambda__1___closed__1);
l_Lean_Meta_Split_splitMatch___lambda__1___closed__2 = _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lambda__1___closed__2);
l_Lean_Meta_Split_splitMatch___lambda__1___closed__3 = _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lambda__1___closed__3);
l_Lean_Meta_Split_splitMatch___lambda__1___closed__4 = _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lambda__1___closed__4);
l_Lean_Meta_Split_splitMatch___lambda__1___closed__5 = _init_l_Lean_Meta_Split_splitMatch___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lambda__1___closed__5);
l_Lean_Meta_splitTarget_x3f_go___closed__1 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__1);
l_Lean_Meta_splitTarget_x3f_go___closed__2 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__2();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__2);
l_Lean_Meta_splitTarget_x3f_go___closed__3 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__3();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__3);
l_Lean_Meta_splitTarget_x3f_go___closed__4 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__4();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__4);
l_Lean_Meta_splitTarget_x3f_go___closed__5 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__5();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__5);
l_Lean_Meta_splitTarget_x3f_go___closed__6 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__6();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__6);
l_Lean_Meta_splitTarget_x3f_go___closed__7 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__7();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__7);
l_Lean_Meta_splitTarget_x3f_go___closed__8 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__8();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__8);
l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lambda__1___closed__1);
l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lambda__1___closed__2);
l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__15);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__16);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812____closed__17);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6812_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
